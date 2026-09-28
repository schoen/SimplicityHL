use std::collections::{HashMap, HashSet};

use crate::driver::{DependencyGraph, CRATE_STR, MAIN_MODULE, MAIN_STR};
use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::parse::{self, Visibility};
use crate::resolution::is_valid_dependency_identifier;
use crate::source::CanonPath;
use crate::str::{Identifier, ModuleName};

/// A file's items, placed at the module path the file occupies.
///
/// Files that share a path prefix share the modules along it, so the tree
/// merges them: `lib/base.simf` and `lib/left.simf` both live under one
/// `mod lib`. Children keep the order they were inserted in, which is the
/// driver's topological load order.
#[derive(Default)]
struct ModuleTree {
    /// The items of the file whose path ends exactly here, if any.
    items: Vec<parse::Item>,
    /// A file id to attribute this module's span to, for diagnostics.
    file_id: Option<usize>,
    children: Vec<(ModuleName, ModuleTree)>,
}

impl ModuleTree {
    /// Place `items` at `path`, creating the modules along the way.
    fn insert(&mut self, path: &[ModuleName], file_id: usize, items: Vec<parse::Item>) {
        if self.file_id.is_none() {
            self.file_id = Some(file_id);
        }

        let Some((head, rest)) = path.split_first() else {
            self.items.extend(items);
            return;
        };

        match self.children.iter().position(|(name, _)| name == head) {
            Some(index) => self.children[index].1.insert(rest, file_id, items),
            None => {
                let mut child = Self::default();
                child.insert(rest, file_id, items);
                self.children.push((head.shallow_clone(), child));
            }
        }
    }

    /// Flatten the tree into items.
    ///
    /// Submodules come before the node's own items, so a file's dependencies
    /// are analyzed before the file that imports them.
    fn into_items(self) -> Vec<parse::Item> {
        let file_id = self.file_id.unwrap_or(MAIN_MODULE);
        let mut out = Vec::with_capacity(self.children.len() + self.items.len());

        for (name, child) in self.children {
            let inner = child.into_items();
            out.push(parse::Item::Module(parse::Module::new(
                file_id,
                // The module exists so that the items the user imported can
                // be reached through it; `pub` on the items themselves is
                // what actually governs access.
                Visibility::Public,
                name,
                &inner,
            )));
        }

        out.extend(self.items);
        out
    }
}

/// Reject a module declared in the entry file whose name collides with the
/// module a dependency's directory contributes at the root.
///
/// The entry file's items sit at the root of the flattened program beside
/// those modules, so the two can collide. The user owns both names here --
/// the module they wrote and the directory they pointed a dependency at --
/// so rejecting the collision is actionable.
fn forbid_root_module_collision(
    local_items: &[parse::Item],
    occupied: &HashSet<ModuleName>,
    diagnostics: &mut DiagnosticManager,
) {
    for item in local_items {
        let parse::Item::Module(module) = item else {
            continue;
        };

        if !occupied.contains(module.name()) {
            continue;
        }

        diagnostics.push(Diagnostic::new(
            Error::Grammar {
                msg: format!(
                    "module `{}` has the same name as the module a dependency of this \
                     program contributes; rename one of them",
                    module.name()
                ),
            },
            *module.span(),
        ));
    }
}

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Resolves the dependency graph and constructs the final AST program.
    pub(crate) fn linearize_and_assemble(
        &self,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<parse::Program> {
        match self.linearize() {
            Ok(order) => {
                diagnostics.with_source_order(&order);
                self.assemble_program(&order, diagnostics)
            }
            Err(err) => {
                diagnostics.push(err);
                None
            }
        }
    }

    /// The package root that owns the entry file.
    ///
    /// Files under it are part of the program itself; files under any other
    /// package root belong to a dependency.
    fn entry_package_root(&self, diagnostics: &mut DiagnosticManager) -> Option<CanonPath> {
        let entry = self.sources.path(MAIN_MODULE)?;
        match self.dependency_map.get_package_root(entry) {
            Some(root) => Some(root.clone()),
            None => {
                diagnostics.push(Diagnostic::file(
                    Error::Internal {
                        msg: "the entry file is not inside any package root".to_owned(),
                    },
                    MAIN_MODULE,
                ));
                None
            }
        }
    }

    /// The module path a file's items occupy in the flattened program.
    ///
    /// The path is the file's location relative to the root of the package
    /// that owns it, with the directory name of the package prefixed when the
    /// file belongs to a dependency. So `libs/lib/A.simf` reached through a
    /// dependency rooted at `libs/lib` becomes `lib::A`, and `utils/math.simf`
    /// inside the program itself becomes `utils::math`.
    ///
    /// The entry file is not wrapped, so its path is empty.
    ///
    /// Every segment is a name the user chose -- a directory or a file stem --
    /// so it has to be a legal identifier, and a segment that is not is
    /// reported here rather than producing an unnameable module.
    fn module_path_of(
        &self,
        source_id: usize,
        entry_root: &CanonPath,
    ) -> Result<Vec<ModuleName>, Diagnostic> {
        // Walk up the chain of `mod name;` declarations. Each one was written
        // by hand, so it settles where the file sits.
        let mut declared = Vec::new();
        let mut current = source_id;
        while let Some((parent, name)) = self.declared_parents.get(&current) {
            declared.push(name.shallow_clone());
            current = *parent;
        }
        declared.reverse();

        // The file the chain ends at has no declared position: it is the entry
        // file, or one a `use` brought in. Its own position is derived.
        let mut path = self.derived_module_path(current, entry_root)?;
        path.extend(declared);
        Ok(path)
    }

    /// The module path a file's items occupy when nothing declares it, derived
    /// from where the file sits on disk.
    fn derived_module_path(
        &self,
        source_id: usize,
        entry_root: &CanonPath,
    ) -> Result<Vec<ModuleName>, Diagnostic> {
        if source_id == MAIN_MODULE {
            return Ok(Vec::new());
        }

        let internal = |msg: String| Diagnostic::file(Error::Internal { msg }, source_id);

        let path = self
            .sources
            .path(source_id)
            .ok_or_else(|| internal(format!("source {source_id} is not registered")))?;

        let package_root = self
            .dependency_map
            .get_package_root(path)
            .ok_or_else(|| internal("file is not inside any package root".to_owned()))?;

        let relative = path
            .as_path()
            .strip_prefix(package_root.as_path())
            .map_err(|_| internal("file is not inside its own package root".to_owned()))?;

        let mut segments: Vec<String> = Vec::new();

        // A dependency is a module of its own, named after its directory.
        if package_root != entry_root {
            let name = package_root
                .as_path()
                .file_name()
                .and_then(std::ffi::OsStr::to_str)
                .ok_or_else(|| internal("dependency root has no directory name".to_owned()))?;
            segments.push(name.to_owned());
        }

        if let Some(parent) = relative.parent() {
            for component in parent.iter() {
                let segment = component
                    .to_str()
                    .ok_or_else(|| internal("path component is not valid UTF-8".to_owned()))?;
                segments.push(segment.to_owned());
            }
        }

        let stem = relative
            .file_stem()
            .and_then(std::ffi::OsStr::to_str)
            .ok_or_else(|| internal("file has no stem".to_owned()))?;
        segments.push(stem.to_owned());

        for segment in &segments {
            if !is_valid_dependency_identifier(segment) {
                return Err(Diagnostic::file(
                    Error::Grammar {
                        msg: format!(
                            "`{segment}` is used as a module name but is not a valid \
                             identifier; rename the file or directory"
                        ),
                    },
                    source_id,
                ));
            }
        }

        Ok(segments
            .iter()
            .map(|segment| ModuleName::from_str_unchecked(segment))
            .collect())
    }

    /// The module path of every file in `order`, or `None` if any file could
    /// not be placed. Two files may not occupy the same path.
    fn module_paths(
        &self,
        order: &[usize],
        entry_root: &CanonPath,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<HashMap<usize, Vec<ModuleName>>> {
        let mut paths = HashMap::with_capacity(order.len());
        let mut taken: HashMap<Vec<ModuleName>, usize> = HashMap::with_capacity(order.len());
        let mut failed = false;

        for &source_id in order {
            let path = match self.module_path_of(source_id, entry_root) {
                Ok(path) => path,
                Err(err) => {
                    diagnostics.push(err);
                    failed = true;
                    continue;
                }
            };

            if let Some(&other) = taken.get(&path) {
                let rendered = path
                    .iter()
                    .map(ModuleName::as_str)
                    .collect::<Vec<_>>()
                    .join("::");
                let other_file = self
                    .sources
                    .entry(other)
                    .map_or_else(|| "another file".to_owned(), |e| e.str_name());

                diagnostics.push(Diagnostic::file(
                    Error::Grammar {
                        msg: format!(
                            "this file would be the module `{rendered}`, which is already \
                             occupied by `{other_file}`; rename one of them"
                        ),
                    },
                    source_id,
                ));
                failed = true;
                continue;
            }

            taken.insert(path.clone(), source_id);
            paths.insert(source_id, path);
        }

        (!failed).then_some(paths)
    }

    /// Constructs the unified array of items for the entire multi-program.
    fn assemble_program(
        &self,
        order: &[usize],
        diagnostics: &mut DiagnosticManager,
    ) -> Option<parse::Program> {
        let entry_root = self.entry_package_root(diagnostics)?;
        let module_paths = self.module_paths(order, &entry_root, diagnostics)?;

        // The names a dependency's directory contributes at the root, which
        // the entry file's own modules must not collide with.
        let occupied: HashSet<ModuleName> = module_paths
            .iter()
            .filter(|(&source_id, _)| source_id != MAIN_MODULE)
            .filter_map(|(_, path)| path.first().map(ModuleName::shallow_clone))
            .collect();

        let target_ids: HashMap<Span, usize> = self
            .use_cache
            .iter()
            .map(|(span, resolved)| {
                let id = self
                    .sources
                    .id(&resolved.path)
                    .expect("resolved path must be registered in source map");
                (*span, id)
            })
            .collect();

        let mut tree = ModuleTree::default();

        for &source_id in order {
            let module = &self.modules[&source_id];

            let local_items: Vec<parse::Item> = module
                .program
                .items()
                .iter()
                .filter_map(|item| self.rewrite_item(item, &target_ids, &module_paths))
                .collect();

            if source_id == MAIN_MODULE {
                let has_main = local_items
                    .iter()
                    .any(|item| matches!(item, parse::Item::Function(f) if f.name() == MAIN_STR));

                if !has_main {
                    diagnostics.push(Diagnostic::global(Error::CannotParse {
                        msg: Error::MainOutOfEntryFile.to_string(),
                    }));
                }

                forbid_root_module_collision(&local_items, &occupied, diagnostics);
            }

            tree.insert(&module_paths[&source_id], source_id, local_items);
        }

        let items = tree.into_items();

        (!diagnostics.has_errors())
            .then(|| parse::Program::new(&items, *self.modules[&MAIN_MODULE].program.as_ref()))
    }

    /// Rewrites a single item for the flattened single-file representation.
    fn rewrite_item(
        &self,
        item: &parse::Item,
        target_ids: &HashMap<Span, usize>,
        module_paths: &HashMap<usize, Vec<ModuleName>>,
    ) -> Option<parse::Item> {
        match item {
            parse::Item::Use(use_decl) => {
                Some(self.rewrite_use(use_decl, target_ids, module_paths))
            }
            // The tree places the declared file's items at this position, so
            // the declaration itself would be a second, empty module of the
            // same name.
            parse::Item::Module(module) if module.is_from_file() => None,
            parse::Item::Module(module) => {
                let items: Vec<parse::Item> = module
                    .items()
                    .iter()
                    .filter_map(|inner_item| self.rewrite_item(inner_item, target_ids, module_paths))
                    .collect();

                Some(parse::Item::Module(parse::Module::new(
                    module.span().file_id,
                    module.visibility().clone(),
                    module.name().clone(),
                    &items,
                )))
            }
            parse::Item::TypeAlias(_)
            | parse::Item::Function(_)
            | parse::Item::EnumDeclaration(_) => Some(item.clone()),
            parse::Item::Ignored => None,
        }
    }

    /// Rewrites a `use` declaration into its canonical `crate`-rooted form.
    ///
    /// The resolved path becomes `crate::<module path of the target file>::<mod_path...>`.
    /// A `use` pointing into the entry file keeps its `mod_path` alone, since
    /// the entry file's items are not wrapped.
    ///
    /// ## Example
    ///
    /// - `use base_math::simple_op::hash` → `use crate::math::simple_op::hash`
    /// - `use crate::inline_mod::item` → `use crate::inline_mod::item`
    fn rewrite_use(
        &self,
        use_decl: &parse::UseDecl,
        target_ids: &HashMap<Span, usize>,
        module_paths: &HashMap<usize, Vec<ModuleName>>,
    ) -> parse::Item {
        let span = *use_decl.span();
        let resolved = &self.use_cache[&span];
        let target_id = target_ids[&span];
        let target_path = module_paths
            .get(&target_id)
            .map_or(&[] as &[ModuleName], Vec::as_slice);

        let mut new_path = Vec::with_capacity(target_path.len() + resolved.mod_path.len() + 1);
        new_path.push(Identifier::from_str_unchecked(CRATE_STR));
        new_path.extend(
            target_path
                .iter()
                .map(|segment| Identifier::from_str_unchecked(segment.as_str())),
        );
        new_path.extend(resolved.mod_path.iter().cloned());

        let mut use_decl = use_decl.clone();
        use_decl.set_path(&new_path);
        parse::Item::Use(use_decl)
    }
}

#[cfg(test)]
mod flattening_tests {
    use crate::driver::tests::setup_graph;
    use crate::driver::CRATE_STR;
    use crate::error::{Diagnostic, Error, Location, Span};
    use crate::parse;

    use std::collections::HashMap;

    // Helper to get the built program
    fn build_flattened_program(
        files: Vec<(&str, &str)>,
    ) -> (parse::Program, HashMap<String, usize>) {
        let (graph, ids, _dir, mut diagnostics) = setup_graph(files);

        let Some(program) = graph.linearize_and_assemble(&mut diagnostics) else {
            panic!("{}", &diagnostics);
        };

        (program, ids)
    }

    /// Find a module by name among `items`.
    fn find_module<'a>(items: &'a [parse::Item], name: &str) -> Option<&'a parse::Module> {
        items.iter().find_map(|item| match item {
            parse::Item::Module(m) => (m.name().as_str() == name).then_some(m),
            _ => None,
        })
    }

    #[test]
    fn entry_file_items_are_spliced_at_the_root() {
        // The entry file must not be wrapped: `fn main` stays at the top
        // level, so flattening is idempotent and types declared there keep
        // an empty module path.
        let (program, _ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn dep_func() {}"),
            ("main.simf", "use lib::A::dep_func; fn main() {}"),
        ]);

        let has_root_main = program
            .items()
            .iter()
            .any(|item| matches!(item, parse::Item::Function(f) if f.name() == "main"));
        assert!(
            has_root_main,
            "`fn main` must live at the root of the flattened program"
        );
    }

    #[test]
    fn dependency_is_nested_under_its_declared_names() {
        // A dependency file lands at the module path its directory and file
        // name spell, not at a compiler-generated name.
        let (program, _ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn dep_func() {}"),
            ("main.simf", "use lib::A::dep_func; fn main() {}"),
        ]);

        let lib = find_module(program.items(), "lib")
            .expect("the dependency should live under `mod lib`");
        let file = find_module(lib.items(), "A").expect("its file should live under `mod A`");

        let has_dep_func = file
            .items()
            .iter()
            .any(|item| matches!(item, parse::Item::Function(f) if f.name() == "dep_func"));
        assert!(has_dep_func, "`mod lib::A` must hold the dependency's items");
    }

    #[test]
    fn program_owned_subdirectory_keeps_its_own_path() {
        // A file belonging to the program itself is not prefixed by a
        // dependency name: it keeps its path relative to the project root.
        let (program, _ids) = build_flattened_program(vec![
            ("utils/math.simf", "pub fn add() {}"),
            ("main.simf", "use crate::utils::math::add; fn main() {}"),
        ]);

        let utils =
            find_module(program.items(), "utils").expect("`utils/` should become `mod utils`");
        assert!(
            find_module(utils.items(), "math").is_some(),
            "`utils/math.simf` should become `mod utils::math`"
        );
    }

    #[test]
    fn a_module_declaration_brings_in_a_file_no_use_mentions() {
        // `use` cannot reach this file: nothing imports from it. Only the
        // declaration brings it into the program.
        let (program, _ids) = build_flattened_program(vec![
            ("extra.simf", "pub fn unused_here() {}"),
            ("main.simf", "mod extra; fn main() {}"),
        ]);

        let extra =
            find_module(program.items(), "extra").expect("`mod extra;` must load `extra.simf`");
        assert!(
            extra
                .items()
                .iter()
                .any(|item| matches!(item, parse::Item::Function(f) if f.name() == "unused_here")),
            "the declared module must hold the file's items"
        );
    }

    #[test]
    fn a_module_declaration_does_not_survive_beside_what_it_declared() {
        let (program, _ids) = build_flattened_program(vec![
            ("helper.simf", "pub fn add() {}"),
            ("main.simf", "mod helper; use crate::helper::add; fn main() {}"),
        ]);

        let named_helper = program
            .items()
            .iter()
            .filter(|item| {
                matches!(item, parse::Item::Module(m) if m.name().as_str() == "helper")
            })
            .count();
        assert_eq!(
            named_helper, 1,
            "the declaration must be replaced by the module, not sit beside it"
        );
    }

    #[test]
    fn a_module_declaration_inside_a_module_is_rejected() {
        let (graph, _ids, _ws, diagnostics) = crate::driver::tests::setup_graph_raw(vec![
            ("helper.simf", "pub fn add() {}"),
            ("main.simf", "mod outer { mod helper; } fn main() {}"),
        ]);

        assert!(graph.is_none(), "a nested module declaration must fail");
        assert!(
            diagnostics.render_to_string().contains("top level of a file"),
            "the error should say where a module declaration may appear: {diagnostics}"
        );
    }

    #[test]
    fn a_module_declaration_naming_no_file_is_rejected() {
        let (graph, _ids, _ws, diagnostics) =
            crate::driver::tests::setup_graph_raw(vec![("main.simf", "mod missing; fn main() {}")]);

        assert!(graph.is_none(), "a declaration with no file must fail");
        assert!(
            diagnostics.render_to_string().contains("missing.simf"),
            "the error should name the file it looked for: {diagnostics}"
        );
    }

    #[test]
    fn test_use_paths_are_rewritten_to_canonical_files() {
        // Scenario: When main.simf says `use lib::A::foo`, the flattener must
        // rewrite this path to `use crate::lib::A::foo`.
        let (program, _ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        // The entry file is not wrapped, so its `use` sits at the root.
        let use_decl = program
            .items()
            .iter()
            .find_map(|item| {
                if let parse::Item::Use(u) = item {
                    Some(u)
                } else {
                    None
                }
            })
            .expect("The entry file's use declaration should be at the root");

        let path = use_decl.path();
        assert_eq!(path.len(), 3, "expected `crate::lib::A`, got {path:?}");
        assert_eq!(path[0], *CRATE_STR, "Path must start with `crate`");
        assert_eq!(path[1], *"lib", "Path must route through the dependency name");
        assert_eq!(path[2], *"A", "Path must route through the file name");
    }

    #[test]
    fn dependency_main_does_not_satisfy_missing_root_main() {
        let (graph, _ids, _dir, mut diagnostics) = setup_graph(vec![
            ("main.simf", "use lib::A::helper;"),
            (
                "libs/lib/A.simf",
                "fn main() { assert!(false); } pub fn helper() {}",
            ),
        ]);

        let driver_program = graph.linearize_and_assemble(&mut diagnostics);

        assert!(
            driver_program.is_none(),
            "Expected the build to fail and return None, but got: {:?}",
            driver_program
        );

        assert!(
            diagnostics.has_errors(),
            "a dependency `fn main` must not satisfy a missing entrypoint `fn main`"
        );
    }

    #[test]
    fn driver_supplies_dependency_order_for_diagnostic_presentation() {
        let (graph, ids, _dir, mut diagnostics) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn helper() {}"),
            ("main.simf", "use lib::A::helper; fn main() {}"),
        ]);
        let main_id = ids["main"];
        let dependency_id = ids["A"];

        diagnostics.push(Diagnostic::new(
            Error::CannotParse {
                msg: "entry".to_owned(),
            },
            Span::new(main_id, 0..1),
        ));
        diagnostics.push(Diagnostic::new(
            Error::CannotParse {
                msg: "dependency".to_owned(),
            },
            Span::new(dependency_id, 0..1),
        ));

        let _ = graph.linearize_and_assemble(&mut diagnostics);
        assert!(matches!(
            diagnostics.diagnostics()[0].location(),
            Location::Code(span) if span.file_id == main_id
        ));
        assert!(matches!(
            diagnostics.presentation_order()[0].location(),
            Location::Code(span) if span.file_id == dependency_id
        ));
    }
}

#[cfg(test)]
mod dependency_map_tests {
    use crate::driver::tests::setup_graph;
    use crate::error::DiagnosticManager;

    // Helper to run the driver and return the error collector so we can inspect it.
    fn run_driver(files: Vec<(&str, &str)>) -> DiagnosticManager {
        let (graph, _ids, _dir, mut diagnostics) = setup_graph(files);
        let _ = graph.linearize_and_assemble(&mut diagnostics).unwrap();
        diagnostics
    }

    #[test]
    fn test_crate_path_resolves_to_physical_file() {
        // Scenario: `crate::utils::math` should map to the physical `utils/math.simf` file.
        let diagnostics = run_driver(vec![
            ("utils/math.simf", "pub fn add() {}"),
            ("main.simf", "use crate::utils::math::add; fn main() {}"),
        ]);

        assert!(
            !diagnostics.has_errors(),
            "Driver should successfully find the physical file 'utils/math.simf'. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_crate_path_fallback_to_inline_module() {
        // Scenario: `brother.simf` does NOT exist. `crate::brother` must fallback
        // to `main.simf` and treat `brother` as an inline mod_path.
        let diagnostics = run_driver(vec![(
            "main.simf",
            "
                mod brother { pub fn toy() {} }
                use crate::brother::toy;
                fn main() {}
            ",
        )]);

        assert!(
            !diagnostics.has_errors(),
            "Driver must fallback to main.simf for inline modules without throwing FileNotFound. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_crate_path_deeply_nested_inline_fallback() {
        // Scenario: A physical file exists (`utils.simf`), but the REST of the path is inline modules!
        let diagnostics = run_driver(vec![
            (
                "utils.simf",
                "pub mod deeply { pub mod nested { pub fn func() {} } }",
            ),
            (
                "main.simf",
                "use crate::utils::deeply::nested::func; fn main() {}",
            ),
        ]);

        assert!(
            !diagnostics.has_errors(),
            "Driver must split the path at the file boundary correctly. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_external_dependency_resolution() {
        // Scenario: Resolving `use lib::A::foo` across the remapping boundary.
        let diagnostics = run_driver(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        assert!(
            !diagnostics.has_errors(),
            "External dependency resolution via drp_name failed. Errors: {}",
            diagnostics
        );
    }
}
