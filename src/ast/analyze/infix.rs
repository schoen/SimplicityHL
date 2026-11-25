//! Type checking of operators.
//!
//! Each operator is rewritten into an equivalent parse-tree expression that the
//! rest of the checker already handles: a jet call, a type cast, or a `match`
//! on a boolean. The rewritten expression is then checked in place of the
//! operator, so the abstract syntax tree doesn't contain any operator nodes.

use crate::error::{Error, Span, WithSpan};
use crate::jet::target_type;
use crate::num::Pow2Usize;
use crate::parse::{self, InfixOp};
use crate::pattern::Pattern;
use crate::types::{AliasedType, ResolvedType, TypeConstructible, TypeDeconstructible, UIntType};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{SingleExpression, SingleExpressionInner};
use super::AbstractSyntaxTree;

/// Analyze `lhs op rhs`, which must be of type `ty`.
pub(super) fn analyze_binary(
    from: &parse::BinaryOp,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<SingleExpressionInner, Failure> {
    let span = *from.span();
    let lhs = from.lhs().clone();
    let rhs = from.rhs().clone();

    let rewritten = match from.op() {
        // `a && b` is `match a { false => false, true => b }`, which doesn't
        // evaluate `b` when `a` is false.
        InfixOp::And => {
            expect_boolean(ty).with_span(from)?;
            parse::SingleExpression::bool_match(lhs, boolean(false, span), rhs, span)
        }
        // `a || b` is `match a { false => b, true => true }`, which doesn't
        // evaluate `b` when `a` is true.
        InfixOp::Or => {
            expect_boolean(ty).with_span(from)?;
            parse::SingleExpression::bool_match(lhs, rhs, boolean(true, span), span)
        }
        InfixOp::BitAnd => bitwise(BitwiseJet::And, vec![lhs, rhs], ty, span).with_span(from)?,
        InfixOp::BitOr => bitwise(BitwiseJet::Or, vec![lhs, rhs], ty, span).with_span(from)?,
        InfixOp::BitXor => bitwise(BitwiseJet::Xor, vec![lhs, rhs], ty, span).with_span(from)?,
        op
        @ (InfixOp::Eq | InfixOp::Ne | InfixOp::Lt | InfixOp::Le | InfixOp::Gt | InfixOp::Ge) => {
            expect_boolean(ty).with_span(from)?;
            let operand_ty = operand_type(&lhs, scope)
                .or_else(|| operand_type(&rhs, scope))
                .ok_or(Error::OperatorOperandTypeUnknown { op: op.as_str() })
                .with_span(from)?;
            comparison(op, lhs, rhs, &operand_ty, span).with_span(from)?
        }
    };

    analyze_rewritten(&rewritten, ty, scope)
}

/// Analyze `!operand`, which must be of type `ty`.
///
/// `!` is the bitwise complement, which on booleans is logical negation, as
/// in Rust. `!a` on a boolean is
/// `<u1>::into(jet::complement_1(<bool>::into(a)))`, which costs less than a
/// `match`.
pub(super) fn analyze_not(
    from: &parse::Not,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<SingleExpressionInner, Failure> {
    let span = *from.span();
    let rewritten = bitwise(BitwiseJet::Not, vec![from.operand().clone()], ty, span)
        .with_span(from)?;

    analyze_rewritten(&rewritten, ty, scope)
}

fn analyze_rewritten(
    rewritten: &parse::SingleExpression,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<SingleExpressionInner, Failure> {
    SingleExpression::analyze(rewritten, ty, scope).map(|single| single.inner)
}

/// Logical operators produce a boolean, so the context must expect one.
fn expect_boolean(ty: &ResolvedType) -> Result<(), Error> {
    if ty.is_boolean() {
        Ok(())
    } else {
        Err(Error::ExpressionTypeMismatch {
            expected: ty.clone(),
            found: ResolvedType::boolean(),
        })
    }
}

/// The jets `and_N`, `or_N` and `xor_N` of a bitwise operator, and the jets
/// `complement_N` of `!`.
#[derive(Clone, Copy)]
enum BitwiseJet {
    And,
    Or,
    Xor,
    Not,
}

impl BitwiseJet {
    /// The operator that the jets implement, as written in source code.
    fn symbol(self) -> &'static str {
        match self {
            Self::And => InfixOp::BitAnd.as_str(),
            Self::Or => InfixOp::BitOr.as_str(),
            Self::Xor => InfixOp::BitXor.as_str(),
            Self::Not => "!",
        }
    }

    /// The name of the jet for operands of the given width, which is 1, 8,
    /// 16, 32 or 64.
    fn name(self, width: usize) -> String {
        let family = match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
            Self::Not => "complement",
        };
        format!("{family}_{width}")
    }
}

/// The jets `eq_N`, `lt_N` and `le_N` that comparisons are built from.
#[derive(Clone, Copy)]
enum CompareJet {
    Eq,
    Lt,
    Le,
}

impl CompareJet {
    /// Whether the jet exists for operands of the given width.
    fn exists(self, width: usize) -> bool {
        match self {
            Self::Eq => matches!(width, 1 | 8 | 16 | 32 | 64 | 256),
            Self::Lt | Self::Le => matches!(width, 8 | 16 | 32 | 64),
        }
    }

    /// The name of the jet for operands of the given width.
    fn name(self, width: usize) -> String {
        let family = match self {
            Self::Eq => "eq",
            Self::Lt => "lt",
            Self::Le => "le",
        };
        format!("{family}_{width}")
    }
}

/// Rewrite a bitwise operator into jets for the width of `ty`, which is the
/// type of every operand and of the result. `operands` are the two operands
/// of `&`, `|` or `^`, or the one operand of `!`.
fn bitwise(
    jet: BitwiseJet,
    operands: Vec<parse::Expression>,
    ty: &ResolvedType,
    span: Span,
) -> Result<parse::SingleExpression, Error> {
    // A boolean has the same representation as a `u1`, so the `u1` jet works
    // on booleans after a cast in each direction:
    // `<u1>::into(jet::and_1(<bool>::into(a), <bool>::into(b)))`.
    if ty.is_boolean() {
        let operands = operands
            .into_iter()
            .map(|operand| bool_to_u1(operand, span))
            .collect();
        let result = jet_call(&jet.name(1), operands, span);
        return Ok(parse::SingleExpression::from_expression(u1_to_bool(
            result, span,
        )));
    }

    let Some(int) = ty.as_integer() else {
        return Err(Error::OperatorUnsupportedType {
            op: jet.symbol(),
            ty: ty.clone(),
        });
    };
    let width = int.bit_width().get();

    // There are no jets for `u2` and `u4`: use the `u8` jet on zero-extended
    // operands and keep the low bits of the result.
    if matches!(int, UIntType::U2 | UIntType::U4) {
        let operands = operands
            .into_iter()
            .map(|operand| extend_to_u8(operand, int, span))
            .collect();
        let extended = jet_call(&jet.name(8), operands, span);
        return Ok(parse::SingleExpression::jet_call(
            &format!("rightmost_8_{width}"),
            vec![extended],
            span,
        ));
    }

    Ok(parse::SingleExpression::from_expression(bitwise_jets(
        jet, operands, width, span,
    )))
}

/// Apply the bitwise jet to operands of the given width. Above 64 bits,
/// where there are no jets, split the operands into 64-bit limbs (see
/// [`split_into_limbs`]), apply the jet to the limbs at each position, and
/// join the results. For `a & b` on `u128`:
///
/// ```text
/// {
///     let ((lhs_1, lhs_0), (rhs_1, rhs_0)): ((u64, u64), (u64, u64)) =
///         <(u128, u128)>::into((a, b));
///     <(u64, u64)>::into((jet::and_64(lhs_1, rhs_1), jet::and_64(lhs_0, rhs_0)))
/// }
/// ```
fn bitwise_jets(
    jet: BitwiseJet,
    operands: Vec<parse::Expression>,
    width: usize,
    span: Span,
) -> parse::Expression {
    if width <= 64 {
        return jet_call(&jet.name(width), operands, span);
    }

    let (split, limbs) = split_into_limbs(operands, width, span);
    let results = (0..width / 64)
        .map(|position| {
            let args = limbs
                .iter()
                .map(|names| variable(&names[position], span))
                .collect();
            jet_call(&jet.name(64), args, span)
        })
        .collect();
    let joined =
        parse::SingleExpression::type_cast(limbs_type(width), limbs_tuple(results, span), span)
            .into_expression();
    parse::SingleExpression::block(vec![split], joined, span)
}

/// Rewrite a comparison of two operands of type `operand_ty` into jet calls.
fn comparison(
    op: InfixOp,
    lhs: parse::Expression,
    rhs: parse::Expression,
    operand_ty: &ResolvedType,
    span: Span,
) -> Result<parse::SingleExpression, Error> {
    let unsupported = || Error::OperatorUnsupportedType {
        op: op.as_str(),
        ty: operand_ty.clone(),
    };

    let (width, lhs, rhs) = if operand_ty.is_boolean() {
        // Booleans compare as `u1`, which has the same representation.
        if !matches!(op, InfixOp::Eq | InfixOp::Ne) {
            return Err(unsupported());
        }
        (1, bool_to_u1(lhs, span), bool_to_u1(rhs, span))
    } else {
        let int = operand_ty.as_integer().ok_or_else(unsupported)?;
        if matches!(int, UIntType::U2 | UIntType::U4) {
            // There are no jets for `u2` and `u4`: compare the operands
            // zero-extended to `u8`.
            (
                8,
                extend_to_u8(lhs, int, span),
                extend_to_u8(rhs, int, span),
            )
        } else {
            (int.bit_width().get(), lhs, rhs)
        }
    };

    let compare = |jet, lhs, rhs| comparison_jets(jet, lhs, rhs, width, span);

    let rewritten = match op {
        InfixOp::Eq => compare(CompareJet::Eq, lhs, rhs),
        InfixOp::Ne => negate(compare(CompareJet::Eq, lhs, rhs), span),
        InfixOp::Lt => compare(CompareJet::Lt, lhs, rhs),
        InfixOp::Le => compare(CompareJet::Le, lhs, rhs),
        // There are no greater-than jets, so `a > b` is `b < a`. This evaluates
        // `b` before `a`. Evaluation doesn't have side effects other than
        // failing and the output of `dbg!`, so the order only decides which
        // failure is reported when both operands fail, and the order of the
        // output of `dbg!` in the operands.
        InfixOp::Gt => compare(CompareJet::Lt, rhs, lhs),
        InfixOp::Ge => compare(CompareJet::Le, rhs, lhs),
        InfixOp::BitAnd | InfixOp::BitOr | InfixOp::BitXor | InfixOp::And | InfixOp::Or => {
            unreachable!("`{op}` is not a comparison operator")
        }
    };
    Ok(parse::SingleExpression::from_expression(rewritten))
}

/// Compare operands of the given width, which is 1, 8, 16, 32, 64, 128 or
/// 256, with the jet, or where the jet doesn't exist for the width, with
/// other jets:
///
/// - On `u1`, `a < b` is `!a & b`, and `a <= b` is `!a | b`.
/// - On `u128`, `a == b` compares the operands zero-extended to `u256`.
/// - On `u128` and `u256`, `a < b` and `a <= b` come from a subtraction
///   (see [`borrow_chain`]).
fn comparison_jets(
    jet: CompareJet,
    lhs: parse::Expression,
    rhs: parse::Expression,
    width: usize,
    span: Span,
) -> parse::Expression {
    if jet.exists(width) {
        return jet_call(&jet.name(width), vec![lhs, rhs], span);
    }

    match (jet, width) {
        (CompareJet::Eq, 128) => {
            let extend = |operand| {
                let zero = parse::SingleExpression::decimal("0", span).into_expression();
                let pair = parse::SingleExpression::tuple(vec![zero, operand], span);
                parse::SingleExpression::type_cast(
                    pair_type(UIntType::U128),
                    pair.into_expression(),
                    span,
                )
                .into_expression()
            };
            jet_call("eq_256", vec![extend(lhs), extend(rhs)], span)
        }
        (CompareJet::Lt | CompareJet::Le, 1) => {
            let combine = match jet {
                CompareJet::Lt => "and_1",
                _ => "or_1",
            };
            let not_lhs = jet_call("complement_1", vec![lhs], span);
            u1_to_bool(jet_call(combine, vec![not_lhs, rhs], span), span)
        }
        (CompareJet::Lt, 128 | 256) => borrow_chain(lhs, rhs, width, false, span),
        (CompareJet::Le, 128 | 256) => borrow_chain(lhs, rhs, width, true, span),
        _ => unreachable!("there is no lowering for `{}`", jet.name(width)),
    }
}

/// Name of the borrow inside [`borrow_chain`].
const BORROW: &str = "borrow";

/// Build a block that computes `a < b`, or with `or_equal`, `a <= b`, for
/// operands of 128 or 256 bits. It splits both operands into 64-bit limbs,
/// and subtracts them from the least significant limb up, passing on the
/// borrow. `a < b` exactly when `a - b` borrows, and `a <= b` exactly when
/// `b - a` doesn't. For `a < b` on `u128`:
///
/// ```text
/// {
///     let ((lhs_1, lhs_0), (rhs_1, rhs_0)): ((u64, u64), (u64, u64)) =
///         <(u128, u128)>::into((a, b));
///     let (borrow, _): (bool, u64) = jet::subtract_64(lhs_0, rhs_0);
///     let (borrow, _): (bool, u64) = jet::full_subtract_64(borrow, lhs_1, rhs_1);
///     borrow
/// }
/// ```
///
/// The names can't capture any variable of the program (see
/// [`split_into_limbs`]).
fn borrow_chain(
    lhs: parse::Expression,
    rhs: parse::Expression,
    width: usize,
    or_equal: bool,
    span: Span,
) -> parse::Expression {
    let (split, limbs) = split_into_limbs(vec![lhs, rhs], width, span);
    let [lhs_limbs, rhs_limbs]: [Vec<String>; 2] =
        limbs.try_into().expect("there are two operands");
    let mut statements = vec![split];

    let (minuend, subtrahend) = if or_equal {
        (&rhs_limbs, &lhs_limbs)
    } else {
        (&lhs_limbs, &rhs_limbs)
    };
    for (i, (minuend, subtrahend)) in minuend.iter().zip(subtrahend).enumerate() {
        let limb_args = [variable(minuend, span), variable(subtrahend, span)];
        let subtraction = if i == 0 {
            jet_call("subtract_64", Vec::from(limb_args), span)
        } else {
            let mut args = vec![variable(BORROW, span)];
            args.extend(limb_args);
            jet_call("full_subtract_64", args, span)
        };
        statements.push(parse::SingleExpression::assignment(
            Pattern::tuple([identifier_pattern(BORROW), Pattern::Ignore]),
            AliasedType::tuple([AliasedType::boolean(), AliasedType::from(UIntType::U64)]),
            subtraction,
            span,
        ));
    }

    let borrow = variable(BORROW, span);
    let result = if or_equal {
        negate(borrow, span)
    } else {
        borrow
    };
    parse::SingleExpression::block(statements, result, span)
}

/// Build the statement that splits one or two operands, of 128 or 256 bits,
/// into 64-bit limbs, and return it with the names of the limbs of each
/// operand, the least significant first. For two operands of type `u128`:
///
/// ```text
/// let ((lhs_1, lhs_0), (rhs_1, rhs_0)): ((u64, u64), (u64, u64)) =
///     <(u128, u128)>::into((a, b));
/// ```
///
/// and for one, `let (operand_1, operand_0): (u64, u64) = <u128>::into(a);`.
///
/// The operands are evaluated, in order, before any name is bound. Code
/// after the statement that refers only to the limbs, and to names it binds
/// itself, can't capture any variable of the program.
fn split_into_limbs(
    mut operands: Vec<parse::Expression>,
    width: usize,
    span: Span,
) -> (parse::Statement, Vec<Vec<String>>) {
    let sides: &[&str] = match operands.len() {
        1 => &["operand"],
        2 => &["lhs", "rhs"],
        n => unreachable!("an operator doesn't have {n} operands"),
    };
    let limbs: Vec<Vec<String>> = sides
        .iter()
        .map(|side| (0..width / 64).map(|i| format!("{side}_{i}")).collect())
        .collect();

    let (pattern, ty, source, value) = if operands.len() == 1 {
        (
            limbs_pattern(&limbs[0]),
            limbs_type(width),
            AliasedType::from(uint(width)),
            operands.pop().expect("there is one operand"),
        )
    } else {
        (
            Pattern::tuple(limbs.iter().map(|names| limbs_pattern(names))),
            AliasedType::tuple([limbs_type(width), limbs_type(width)]),
            pair_type(uint(width)),
            parse::SingleExpression::tuple(operands, span).into_expression(),
        )
    };
    let split = parse::SingleExpression::type_cast(source, value, span).into_expression();
    let statement = parse::SingleExpression::assignment(pattern, ty, split, span);
    (statement, limbs)
}

/// The value of [`limbs_type`] made of `limbs`, which are listed the least
/// significant first.
fn limbs_tuple(mut limbs: Vec<parse::Expression>, span: Span) -> parse::Expression {
    if limbs.len() == 1 {
        return limbs.pop().expect("there is one limb");
    }
    let high = limbs.split_off(limbs.len() / 2);
    parse::SingleExpression::tuple(
        vec![limbs_tuple(high, span), limbs_tuple(limbs, span)],
        span,
    )
    .into_expression()
}

/// The type of an integer of the given width as 64-bit limbs: `u64`,
/// `(u64, u64)` or `((u64, u64), (u64, u64))`.
fn limbs_type(width: usize) -> AliasedType {
    if width == 64 {
        AliasedType::from(UIntType::U64)
    } else {
        let half = limbs_type(width / 2);
        AliasedType::tuple([half.clone(), half])
    }
}

/// The pattern that binds the limbs of [`limbs_type`] to `names`, which are
/// listed the least significant first.
fn limbs_pattern(names: &[String]) -> Pattern {
    match names {
        [name] => identifier_pattern(name),
        _ => {
            let (low, high) = names.split_at(names.len() / 2);
            Pattern::tuple([limbs_pattern(high), limbs_pattern(low)])
        }
    }
}

/// The type `(ty, ty)`.
fn pair_type(ty: UIntType) -> AliasedType {
    AliasedType::tuple([AliasedType::from(ty), AliasedType::from(ty)])
}

/// The unsigned integer type of the given width.
fn uint(width: usize) -> UIntType {
    Pow2Usize::new(width)
        .and_then(UIntType::from_bit_width)
        .unwrap_or_else(|| unreachable!("there is no `u{width}`"))
}

/// The boolean literal `value`.
fn boolean(value: bool, span: Span) -> parse::Expression {
    parse::SingleExpression::boolean(value, span).into_expression()
}

/// The pattern that binds a value to the variable `name`.
fn identifier_pattern(name: &str) -> Pattern {
    Pattern::Identifier(crate::str::Identifier::from_str_unchecked(name))
}

/// The jet call `jet::name(args)`.
fn jet_call(name: &str, args: Vec<parse::Expression>, span: Span) -> parse::Expression {
    parse::SingleExpression::jet_call(name, args, span).into_expression()
}

/// `!operand` for a boolean expression, with the `u1` jet:
/// `<u1>::into(jet::complement_1(<bool>::into(operand)))`.
fn negate(operand: parse::Expression, span: Span) -> parse::Expression {
    let complement = jet_call("complement_1", vec![bool_to_u1(operand, span)], span);
    u1_to_bool(complement, span)
}

/// `<u1>::into(operand)`, which turns a `u1` into the boolean with the same
/// representation.
fn u1_to_bool(operand: parse::Expression, span: Span) -> parse::Expression {
    parse::SingleExpression::type_cast(AliasedType::from(UIntType::U1), operand, span)
        .into_expression()
}

/// A reference to the variable `name`.
fn variable(name: &str, span: Span) -> parse::Expression {
    parse::SingleExpression::variable(name, span).into_expression()
}

/// `<bool>::into(operand)`, which turns a boolean into the `u1` with the same
/// representation.
fn bool_to_u1(operand: parse::Expression, span: Span) -> parse::Expression {
    parse::SingleExpression::type_cast(AliasedType::boolean(), operand, span).into_expression()
}

/// The type of a comparison operand, if it can be found from the operand alone.
///
/// The checker checks each expression against a type that it already knows,
/// but the result type of a comparison, `bool`, doesn't reveal the type of
/// its operands. This finds the type for operands whose type doesn't depend
/// on their context: variables, boolean expressions, and calls of jets and
/// functions. It returns `None` for the rest, such as integer literals,
/// witnesses, parameters and casts, which take their type from their context.
fn operand_type(expression: &parse::Expression, scope: &Scope) -> Option<ResolvedType> {
    use parse::SingleExpressionInner as S;

    // A block's final expression might use variables of the block, which
    // aren't in scope here.
    let parse::ExpressionInner::Single(single) = expression.inner() else {
        return None;
    };

    match single.inner() {
        S::Variable(identifier) => scope.get_variable(identifier).cloned(),
        S::Boolean(_) => Some(ResolvedType::boolean()),
        // `!` has the type of its operand.
        S::Not(not) => operand_type(not.operand(), scope),
        S::Expression(inner) => operand_type(inner, scope),
        S::BinaryOp(binary_op) => match binary_op.op() {
            InfixOp::BitAnd | InfixOp::BitOr | InfixOp::BitXor => {
                operand_type(binary_op.lhs(), scope)
                    .or_else(|| operand_type(binary_op.rhs(), scope))
            }
            _ => Some(ResolvedType::boolean()),
        },
        S::Call(call) => match call.name() {
            parse::CallName::Jet(name) => {
                let jet = scope.jet_hinter().parse_jet(name.as_inner())?;
                target_type(&*jet).resolve_builtin().ok()
            }
            parse::CallName::Custom(name) => scope
                .get_function(name)
                .ok()
                .map(|function| function.ret().clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Zero-extend a `u1`, `u2` or `u4` operand of type `ty` to `u8`, one
/// doubling at a time. `<(u4, u4)>::into((0, x))` is the `u8` whose high half
/// is zero and whose low half is `x`.
fn extend_to_u8(operand: parse::Expression, ty: UIntType, span: Span) -> parse::Expression {
    let mut extended = operand;
    let mut width = ty.bit_width().get();
    while width < 8 {
        let zero = parse::SingleExpression::decimal("0", span).into_expression();
        let pair = parse::SingleExpression::tuple(vec![zero, extended], span).into_expression();
        extended = parse::SingleExpression::type_cast(pair_type(uint(width)), pair, span)
            .into_expression();
        width *= 2;
    }
    extended
}
