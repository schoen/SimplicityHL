//! End-to-end tests of the operators of `-Z infix_operators`: the value of
//! every operator on every type, equivalence with the jet code a programmer
//! would write by hand, operand typing, and error messages.

use std::cmp::Ordering;
use std::fmt::Write as _;

use crate::error::Location;

use super::*;

/// Compile and run `text` with every unstable feature enabled, and require
/// that it succeeds.
fn run(text: &str) {
    TestCase::program_text_with_unstable(Cow::Owned(text.to_owned()), UnstableFeatures::all())
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
}

/// Compile and run `text` with every unstable feature enabled, and require
/// that it fails at run time.
fn run_failure(text: &str) {
    TestCase::program_text_with_unstable(Cow::Owned(text.to_owned()), UnstableFeatures::all())
        .with_witness_values(WitnessValues::default())
        .assert_run_failure();
}

/// Compile `text` without debug symbols and return the CMR of the program.
fn cmr(text: &str) -> simplicity::Cmr {
    CompiledProgram::new_with_unstable(
        text,
        &UnstableFeatures::all(),
        Arguments::default(),
        false,
        Box::new(ElementsJetHinter::new()),
    )
    .unwrap_or_else(|error| panic!("This program should compile:\n{text}\n{error}"))
    .commit()
    .cmr()
}

/// Compile `text`, which must be rejected, and return the message of its
/// first error together with the source text that the error points at.
fn first_error(text: &str) -> (String, String) {
    let diagnostics = match TemplateAst::new_with_unstable(
        text,
        &UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    ) {
        Ok(_) => panic!("Accepted faulty program:\n{text}"),
        Err(diagnostics) => diagnostics,
    };
    let diagnostic = diagnostics
        .diagnostics()
        .first()
        .expect("a rejected program has a diagnostic");
    let Location::Code(span) = diagnostic.location() else {
        panic!("Expected an error in the code, got: {diagnostic}");
    };
    let snippet = span.to_slice(text).expect("span is inside the program");
    (diagnostic.error().to_string(), snippet.to_owned())
}

/// Require that `main_body` is rejected with an error containing `message`.
fn assert_compile_error(main_body: &str, message: &str) {
    let error = operator_compile_error(main_body);
    assert!(
        error.contains(message),
        "Expected an error containing {message:?} for:\n{main_body}\nGot: {error}"
    );
}

// ---------------------------------------------------------------------------
// Value of every operator on every width
// ---------------------------------------------------------------------------

/// An unsigned integer as big-endian bytes, so that comparing the byte
/// strings compares the numbers. Integers narrower than `u8` take one byte.
#[derive(Clone, Debug)]
struct Word {
    bits: usize,
    bytes: Vec<u8>,
}

impl Word {
    fn from_u64(bits: usize, value: u64) -> Self {
        assert!(bits <= 64);
        assert!(
            bits == 64 || value >> bits == 0,
            "{value} doesn't fit in u{bits}"
        );
        let len = bits.div_ceil(8);
        let bytes = value.to_be_bytes()[8 - len..].to_vec();
        Self { bits, bytes }
    }

    fn from_u128(value: u128) -> Self {
        Self {
            bits: 128,
            bytes: value.to_be_bytes().to_vec(),
        }
    }

    /// A `u256` from four 64-bit limbs, the most significant first.
    fn from_limbs(limbs: [u64; 4]) -> Self {
        Self {
            bits: 256,
            bytes: limbs.iter().flat_map(|limb| limb.to_be_bytes()).collect(),
        }
    }

    fn zip(&self, other: &Self, f: impl Fn(u8, u8) -> u8) -> Self {
        Self {
            bits: self.bits,
            bytes: (self.bytes.iter().zip(&other.bytes))
                .map(|(a, b)| f(*a, *b))
                .collect(),
        }
    }

    /// The literal for the value: decimal up to 64 bits and hexadecimal above.
    fn literal(&self) -> String {
        if self.bits <= 64 {
            let mut buffer = [0; 8];
            buffer[8 - self.bytes.len()..].copy_from_slice(&self.bytes);
            u64::from_be_bytes(buffer).to_string()
        } else {
            let mut literal = String::from("0x");
            for byte in &self.bytes {
                write!(literal, "{byte:02x}").unwrap();
            }
            literal
        }
    }
}

/// An expression that is `true` if the integer expressions `x` and `y` of
/// type `u{bits}` are equal. It uses only jets and casts, never an operator.
fn jet_equal(bits: usize, x: &str, y: &str) -> String {
    match bits {
        1 | 8 | 16 | 32 | 64 | 256 => format!("jet::eq_{bits}({x}, {y})"),
        2 => {
            let extend = |e: &str| format!("<(u4, u4)>::into((0, <(u2, u2)>::into((0, {e}))))");
            format!("jet::eq_8({}, {})", extend(x), extend(y))
        }
        4 => {
            let extend = |e: &str| format!("<(u4, u4)>::into((0, {e}))");
            format!("jet::eq_8({}, {})", extend(x), extend(y))
        }
        128 => {
            let extend = |e: &str| format!("<(u128, u128)>::into((0, {e}))");
            format!("jet::eq_256({}, {})", extend(x), extend(y))
        }
        _ => unreachable!("there is no u{bits}"),
    }
}

/// A program that checks every operator on every pair of `values`, all of
/// the same width, against the results computed here.
///
/// The operators are applied once, inside the function `check`, to its
/// parameters. The function checks each result with jets only, and `main`
/// calls it once per pair with the expected results.
fn all_operators_program(values: &[Word]) -> String {
    let bits = values[0].bits;
    let ty = format!("u{bits}");
    let same = |x: &str, y: &str| jet_equal(bits, x, y);
    let same_bool = |e: &str, expected: &str| {
        format!("    assert!(jet::eq_1(<bool>::into({e}), <bool>::into({expected})));\n")
    };

    let mut text = format!(
        "fn check(a: {ty}, b: {ty}, eq: bool, ne: bool, lt: bool, le: bool, gt: bool, ge: bool, \
         bit_and: {ty}, bit_or: {ty}, bit_xor: {ty}) {{\n"
    );
    for (op, expected) in [
        ("==", "eq"),
        ("!=", "ne"),
        ("<", "lt"),
        ("<=", "le"),
        (">", "gt"),
        (">=", "ge"),
    ] {
        text += &same_bool(&format!("a {op} b"), expected);
    }
    for (op, expected) in [("&", "bit_and"), ("|", "bit_or"), ("^", "bit_xor")] {
        writeln!(
            text,
            "    assert!({});",
            same(&format!("a {op} b"), expected)
        )
        .unwrap();
    }
    text += "}\n\nfn main() {\n";

    for a in values {
        for b in values {
            let order = a.bytes.cmp(&b.bytes);
            writeln!(
                text,
                "    check({}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {});",
                a.literal(),
                b.literal(),
                order == Ordering::Equal,
                order != Ordering::Equal,
                order == Ordering::Less,
                order != Ordering::Greater,
                order == Ordering::Greater,
                order != Ordering::Less,
                a.zip(b, |x, y| x & y).literal(),
                a.zip(b, |x, y| x | y).literal(),
                a.zip(b, |x, y| x ^ y).literal(),
            )
            .unwrap();
        }
    }
    text += "}\n";
    text
}

#[test]
fn operators_on_narrow_integers_exhaustively() {
    for bits in [1, 2, 4] {
        let values: Vec<Word> = (0..1u64 << bits)
            .map(|value| Word::from_u64(bits, value))
            .collect();
        run(&all_operators_program(&values));
    }
}

#[test]
fn operators_on_middle_integers_at_boundaries() {
    for bits in [8, 16, 32, 64] {
        let max = u64::MAX >> (64 - bits);
        let half = 1u64 << (bits - 1);
        let values: Vec<Word> = [0, 1, 2, half - 1, half, max - 1, max]
            .into_iter()
            .map(|value| Word::from_u64(bits, value))
            .collect();
        run(&all_operators_program(&values));
    }
}

#[test]
fn operators_on_u128_at_the_split() {
    let high = |n: u128| n << 64;
    let values: Vec<Word> = [
        0,
        1,
        2,
        high(1) - 1,
        high(1),
        high(1) + 1,
        u128::MAX - 1,
        u128::MAX,
        // Pairs that differ only in the high half, only in the low half,
        // and whose halves are ordered in opposite directions.
        high(5) | 7,
        high(9) | 7,
        high(5) | 9,
        high(9) | 5,
    ]
    .into_iter()
    .map(Word::from_u128)
    .collect();
    run(&all_operators_program(&values));
}

#[test]
fn operators_on_u256_at_the_splits() {
    const M: u64 = u64::MAX;
    let values: Vec<Word> = [
        [0, 0, 0, 0],
        [0, 0, 0, 1],
        [M, M, M, M],
        [M, M, M, M - 1],
        // Around the halves, at 2^128.
        [0, 0, M, M],
        [0, 1, 0, 0],
        // Around the quarters, at 2^64 and 2^192.
        [0, 0, 1, 0],
        [0, M, M, M],
        [1, 0, 0, 0],
        // Values that differ in one limb only, and whose limbs are ordered in
        // opposite directions.
        [1, 2, 3, 4],
        [1, 2, 3, 5],
        [1, 2, 4, 3],
        [1, 3, 2, 4],
        [2, 1, 3, 4],
    ]
    .into_iter()
    .map(Word::from_limbs)
    .collect();
    run(&all_operators_program(&values));
}

#[test]
fn operators_on_booleans_exhaustively() {
    let same = |e: &str, expected: &str| {
        format!("    assert!(jet::eq_1(<bool>::into({e}), <bool>::into({expected})));\n")
    };
    let mut text = String::from(
        "fn check(a: bool, b: bool, eq: bool, ne: bool, bit_and: bool, bit_or: bool, \
         bit_xor: bool, and: bool, or: bool, not_a: bool) {\n",
    );
    for (e, expected) in [
        ("a == b", "eq"),
        ("a != b", "ne"),
        ("a & b", "bit_and"),
        ("a | b", "bit_or"),
        ("a ^ b", "bit_xor"),
        ("a && b", "and"),
        ("a || b", "or"),
        ("!a", "not_a"),
    ] {
        text += &same(e, expected);
    }
    text += "}\n\nfn main() {\n";
    for a in [false, true] {
        for b in [false, true] {
            writeln!(
                text,
                "    check({a}, {b}, {}, {}, {}, {}, {}, {}, {}, {});",
                a == b,
                a != b,
                a & b,
                a | b,
                a ^ b,
                a && b,
                a || b,
                !a,
            )
            .unwrap();
        }
    }
    text += "}\n";
    run(&text);
}

#[test]
fn false_comparisons_fail_at_run_time() {
    // A lowering that always gave `true` would pass the tests above only if
    // the checks were wrong, so check that false assertions do fail.
    for (ty, small, big) in [
        ("u1", "0", "1"),
        ("u4", "3", "12"),
        ("u8", "3", "12"),
        ("u64", "3", "12"),
        ("u128", "3", "12"),
        (
            "u256",
            "0x0000000000000000000000000000000000000000000000000000000000000003",
            "0x000000000000000000000000000000000000000000000000000000000000000c",
        ),
    ] {
        for comparison in ["a < b", "a <= b", "b > a", "b >= a", "a == b"] {
            run_failure(&format!(
                "fn main() {{\n    let a: {ty} = {big};\n    let b: {ty} = {small};\n    \
                 assert!({comparison});\n}}\n"
            ));
        }
    }
}

// ---------------------------------------------------------------------------
// Equivalence with hand-written jet code
// ---------------------------------------------------------------------------

/// A program whose `main` checks `body`, with these variables in scope:
/// `a` and `b` of type `u32`, `p` and `q` of type `bool`, `x` and `y` of type
/// `u4`, `s` and `t` of type `u2`, `m` and `n` of type `u1`, `v` and `w` of
/// type `u128`, `g` and `h` of type `u256`.
fn equivalence_program(body: &str) -> String {
    format!(
        "fn f(a: u32, b: u32, p: bool, q: bool, x: u4, y: u4, s: u2, t: u2, m: u1, n: u1, \
         v: u128, w: u128, g: u256, h: u256) -> bool {{
    {body}
}}

fn main() {{
    let g: u256 = 0x0000000000000000000000000000000000000000000000000000000000000001;
    assert!(f(1, 2, true, false, 3, 4, 1, 2, 0, 1, 5, 6, g, g));
}}
"
    )
}

#[test]
fn operators_compile_to_hand_written_jets() {
    let u2_extended = |e: &str| format!("<(u4, u4)>::into((0, <(u2, u2)>::into((0, {e}))))");
    let cases = [
        // Comparisons with a jet of their own.
        ("a == b", "jet::eq_32(a, b)".to_string()),
        ("a < b", "jet::lt_32(a, b)".to_string()),
        ("a <= b", "jet::le_32(a, b)".to_string()),
        ("a > b", "jet::lt_32(b, a)".to_string()),
        ("a >= b", "jet::le_32(b, a)".to_string()),
        (
            "a != b",
            "<u1>::into(jet::complement_1(<bool>::into(jet::eq_32(a, b))))".to_string(),
        ),
        // Bitwise operators with a jet of their own.
        ("jet::eq_32(a & b, 0)", "jet::eq_32(jet::and_32(a, b), 0)".to_string()),
        ("jet::eq_32(a | b, 0)", "jet::eq_32(jet::or_32(a, b), 0)".to_string()),
        ("jet::eq_32(a ^ b, 0)", "jet::eq_32(jet::xor_32(a, b), 0)".to_string()),
        // Logical operators.
        ("p && q", "match p { false => false, true => q, }".to_string()),
        ("p || q", "match p { false => q, true => true, }".to_string()),
        ("!p", "<u1>::into(jet::complement_1(<bool>::into(p)))".to_string()),
        // Operators on booleans that go through `u1`.
        (
            "p == q",
            "jet::eq_1(<bool>::into(p), <bool>::into(q))".to_string(),
        ),
        (
            "p ^ q",
            "<u1>::into(jet::xor_1(<bool>::into(p), <bool>::into(q)))".to_string(),
        ),
        // Narrow integers, extended to `u8`.
        (
            "x < y",
            "jet::lt_8(<(u4, u4)>::into((0, x)), <(u4, u4)>::into((0, y)))".to_string(),
        ),
        (
            "jet::eq_8(<(u4, u4)>::into((0, x & y)), 0)",
            "jet::eq_8(<(u4, u4)>::into((0, jet::rightmost_8_4(jet::and_8(<(u4, u4)>::into((0, x)), <(u4, u4)>::into((0, y)))))), 0)"
                .to_string(),
        ),
        (
            "s >= t",
            format!("jet::le_8({}, {})", u2_extended("t"), u2_extended("s")),
        ),
        // Ordering on `u1`: `a < b` is `!a & b`, and `a <= b` is `!a | b`.
        (
            "m < n",
            "<u1>::into(jet::and_1(jet::complement_1(m), n))".to_string(),
        ),
        (
            "m >= n",
            "<u1>::into(jet::or_1(jet::complement_1(n), m))".to_string(),
        ),
        // Wide integers. The names of the variables that the lowering binds
        // don't matter, because they don't appear in the compiled program.
        (
            "v == w",
            "jet::eq_256(<(u128, u128)>::into((0, v)), <(u128, u128)>::into((0, w)))"
                .to_string(),
        ),
        (
            "v < w",
            "{
        let ((v1, v0), (w1, w0)): ((u64, u64), (u64, u64)) = <(u128, u128)>::into((v, w));
        let (c, _): (bool, u64) = jet::subtract_64(v0, w0);
        let (c, _): (bool, u64) = jet::full_subtract_64(c, v1, w1);
        c
    }"
            .to_string(),
        ),
        (
            "jet::eq_256(g & h, g)",
            "jet::eq_256({
        let (((g3, g2), (g1, g0)), ((h3, h2), (h1, h0))): \
         (((u64, u64), (u64, u64)), ((u64, u64), (u64, u64))) = <(u256, u256)>::into((g, h));
        <((u64, u64), (u64, u64))>::into(((jet::and_64(g3, h3), jet::and_64(g2, h2)), \
         (jet::and_64(g1, h1), jet::and_64(g0, h0))))
    }, g)"
                .to_string(),
        ),
        (
            "g <= h",
            "{
        let (((g3, g2), (g1, g0)), ((h3, h2), (h1, h0))): \
         (((u64, u64), (u64, u64)), ((u64, u64), (u64, u64))) = <(u256, u256)>::into((g, h));
        let (c, _): (bool, u64) = jet::subtract_64(h0, g0);
        let (c, _): (bool, u64) = jet::full_subtract_64(c, h1, g1);
        let (c, _): (bool, u64) = jet::full_subtract_64(c, h2, g2);
        let (c, _): (bool, u64) = jet::full_subtract_64(c, h3, g3);
        <u1>::into(jet::complement_1(<bool>::into(c)))
    }"
            .to_string(),
        ),
    ];

    for (operator, by_hand) in cases {
        assert_eq!(
            cmr(&equivalence_program(operator)),
            cmr(&equivalence_program(&by_hand)),
            "`{operator}` should compile to the same program as `{by_hand}`"
        );
    }
}

#[test]
fn wide_comparisons_do_not_capture_variables() {
    // Ordering and bitwise operators on `u128` and `u256` bind limbs named
    // `lhs_0`, `rhs_0` and so on, and ordering binds a borrow named `borrow`.
    // Variables of the same names must still mean the program's own variables.
    run("fn main() {
    let lhs_0: u128 = 5;
    let rhs_1: u128 = 7;
    let borrow: u128 = 3;
    assert!(lhs_0 < rhs_1);
    assert!(rhs_1 > lhs_0);
    assert!(borrow <= lhs_0);
    assert!(!(lhs_0 >= rhs_1));
    let lhs_3: u256 = 0x0000000000000000000000000000000000000000000000000000000000000005;
    let rhs_0: u256 = 0x0000000000000000000000000000000000000000000000000000000000000007;
    assert!(lhs_3 < rhs_0);
    assert!(!(rhs_0 <= lhs_3));
    assert!(lhs_0 & rhs_1 == 5);
    assert!(borrow | lhs_0 == 7);
    assert!(lhs_3 ^ rhs_0 == 0x0000000000000000000000000000000000000000000000000000000000000002);
}
");
}

// ---------------------------------------------------------------------------
// Operand typing
// ---------------------------------------------------------------------------

#[test]
fn comparison_operand_forms() {
    run("type Amount = u64;
type Flag = bool;

fn sixteen(x: u16) -> u16 {
    x
}

fn amount(x: Amount) -> Amount {
    x
}

fn main() {
    let x: u8 = 3;
    let y: u8 = 5;
    // A literal on the left takes its type from the variable on the right.
    assert!(0 != x);
    assert!(2 < x);
    // Parenthesized operands.
    assert!((x) == 3);
    assert!(((x & 1)) == 1);
    // Bitwise operands, whose type comes from one of their own operands.
    assert!((x & 1) == (y & 1));
    assert!(1 & x == 1);
    // Calls of custom functions and jets.
    assert!(sixteen(9) < 10);
    assert!(jet::current_index() <= 4294967295);
    assert!(jet::lock_time() >= 0);
    // Boolean operands.
    let a: u8 = 1;
    let b: u8 = 2;
    let t: bool = true;
    let f: bool = false;
    assert!((a < b) == (x < y));
    assert!(!t == f);
    assert!(t != (a == b));
    // Type aliases, mixed with the types they stand for.
    let m: Amount = 100;
    let n: u64 = 200;
    assert!(m < n);
    assert!(n > m);
    let masked: Amount = m & n;
    assert!(masked == 64);
    assert!(amount(m) == 100);
    let g: Flag = m < n;
    let h: Flag = !g;
    assert!(g && !h);
    assert!(g != h);
    assert!(g | h);
    // A variable that shadows one of another type.
    let x: u16 = 300;
    assert!(x > 255);
}
");
}

#[test]
fn bitwise_operand_type_comes_from_context() {
    run("fn low_bits(x: u8) -> u8 {
    x & 0x0f
}

fn identity(x: u16) -> u16 {
    x
}

fn main() {
    let a: u16 = 0x0ff0;
    let b: u16 = 0x00ff;
    let c: u8 = 0xa5;
    // Assignments.
    let y: u16 = a & b;
    assert!(jet::eq_16(y, 0x00f0));
    // Function arguments and return values.
    assert!(jet::eq_16(identity(a | b), 0x0fff));
    assert!(jet::eq_8(low_bits(c), 0x05));
    // Tuples, arrays and match arms.
    let t: (u8, bool) = (c ^ 0xff, a < b);
    let (inverted, less): (u8, bool) = t;
    assert!(jet::eq_8(inverted, 0x5a));
    assert!(!less);
    let pair: [u16; 2] = [a & b, a | b];
    let [first, second]: [u16; 2] = pair;
    assert!(jet::eq_16(first, 0x00f0));
    assert!(jet::eq_16(second, 0x0fff));
    let chosen: u16 = match a < b {
        false => a ^ b,
        true => a & b,
    };
    assert!(jet::eq_16(chosen, 0x0f0f));
    // Jet arguments.
    assert!(jet::eq_8(c & 0x0f, 0x05));
}
");
}

#[test]
fn witnesses_and_parameters_take_type_from_other_operand() {
    let text = "fn main() {
    let x: u32 = 1;
    assert!(witness::W == x);
    assert!(param::P < x);
}
";
    let template = TemplateAst::new_with_unstable(
        text,
        &UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    )
    .unwrap_or_else(|error| panic!("{error}"));
    let witness_ty = template
        .witness_types()
        .get(&TemplateProgramWitness::witness_from_str("W"))
        .map(ToString::to_string);
    assert_eq!(witness_ty.as_deref(), Some("u32"));
    let parameter_ty = template
        .parameters()
        .get(&TemplateProgramWitness::parameter_from_str("P"))
        .map(ToString::to_string);
    assert_eq!(parameter_ty.as_deref(), Some("u32"));
}

#[test]
fn operand_types_that_cannot_be_found() {
    for (main_body, op) in [
        ("    assert!(witness::W == 3);", "=="),
        ("    assert!(param::P < 3);", "<"),
        ("    let x: u8 = 1;\n    assert!(<u8>::into(x) == 3);", "=="),
        ("    let x: u8 = 1;\n    assert!(({ x }) != 3);", "!="),
        ("    assert!(3 >= 4);", ">="),
    ] {
        assert_compile_error(
            main_body,
            &format!("Cannot determine the type of the operands of `{op}`"),
        );
    }

    // The error points at the whole comparison.
    let (message, snippet) = first_error("fn main() {\n    assert!(witness::W == 3);\n}\n");
    assert!(message.contains("Cannot determine"), "{message}");
    assert_eq!(snippet, "witness::W == 3");
}

#[test]
fn operators_on_compound_types_are_rejected() {
    for (declaration, ty) in [
        ("let v: (u8, u8) = (1, 2);", "(u8, u8)"),
        ("let v: [u8; 2] = [1, 2];", "[u8; 2]"),
        ("let v: Option<u8> = None;", "Option<u8>"),
        ("let v: Either<u8, u16> = Left(1);", "Either<u8, u16>"),
    ] {
        for op in ["==", "!=", "<", ">="] {
            assert_compile_error(
                &format!("    {declaration}\n    assert!(v {op} v);"),
                &format!("Operator `{op}` cannot be applied to values of type `{ty}`"),
            );
        }
        for op in ["&", "|", "^"] {
            assert_compile_error(
                &format!("    {declaration}\n    let w: {ty} = v {op} v;"),
                &format!("Operator `{op}` cannot be applied to values of type `{ty}`"),
            );
        }
    }

    // An alias of a compound type is rejected with the type it stands for.
    let (message, _) = first_error(
        "type Pair = (u8, u8);\n\nfn main() {\n    let p: Pair = (1, 2);\n    assert!(p == p);\n}\n",
    );
    assert!(
        message.contains("Operator `==` cannot be applied to values of type `(u8, u8)`"),
        "{message}"
    );

    // So is a jet with a tuple result.
    assert_compile_error(
        "    assert!(jet::add_32(1, 2) == (false, 3));",
        "Operator `==` cannot be applied to values of type `(bool, u32)`",
    );
}

#[test]
fn logical_operators_need_booleans() {
    // Ported from PR #232: a non-boolean operand of `&&`.
    for main_body in [
        "    let x: u8 = 1;\n    assert!(true && x);",
        "    let x: u8 = 1;\n    assert!(x && true);",
        "    let x: u8 = 1;\n    assert!(x || true);",
        "    let x: u8 = 1;\n    assert!(!x);",
    ] {
        assert_compile_error(
            main_body,
            "Expected expression of type `bool`, found type `u8`",
        );
    }

    // The error points at the operand.
    let (_, snippet) = first_error("fn main() {\n    let x: u8 = 1;\n    assert!(!x);\n}\n");
    assert_eq!(snippet, "x");
}

// ---------------------------------------------------------------------------
// Error messages from inside the rewritten code
// ---------------------------------------------------------------------------

#[test]
fn errors_point_at_the_faulty_operand() {
    for (text, expected_message, expected_snippet) in [
        // A literal out of range for a narrow type names that type.
        (
            "fn main() {\n    let p: u2 = 1;\n    assert!(p == 5);\n}\n",
            "Value is out of bounds for type `u2`",
            "5",
        ),
        (
            "fn main() {\n    let p: u2 = 1;\n    assert!(5 > p);\n}\n",
            "Value is out of bounds for type `u2`",
            "5",
        ),
        // Mismatched widths, on each side of the operators whose operands
        // are swapped or split.
        (
            "fn main() {\n    let a: u128 = 1;\n    let b: u64 = 2;\n    assert!(a < b);\n}\n",
            "Expected expression of type `u128`, found type `u64`",
            "b",
        ),
        (
            "fn main() {\n    let a: u8 = 1;\n    let b: u16 = 2;\n    assert!(a > b);\n}\n",
            "Expected expression of type `u8`, found type `u16`",
            "b",
        ),
        (
            "fn main() {\n    let a: u16 = 1;\n    let b: u8 = 2;\n    assert!(a >= b);\n}\n",
            "Expected expression of type `u16`, found type `u8`",
            "b",
        ),
        (
            "fn main() {\n    let a: u4 = 1;\n    let b: u2 = 2;\n    assert!(a <= b);\n}\n",
            "Expected expression of type `u4`, found type `u2`",
            "b",
        ),
        // A bitwise result assigned to the wrong type.
        (
            "fn main() {\n    let a: u16 = 1;\n    let y: u8 = a & a;\n}\n",
            "Expected expression of type `u8`, found type `u16`",
            "a",
        ),
    ] {
        let (message, snippet) = first_error(text);
        assert!(
            message.contains(expected_message),
            "Unexpected error for:\n{text}\nGot: {message}"
        );
        assert_eq!(
            snippet, expected_snippet,
            "Error points elsewhere for:\n{text}"
        );
    }
}

// ---------------------------------------------------------------------------
// Example programs
// ---------------------------------------------------------------------------

fn single_witness(name: &str, value: Value) -> WitnessValues {
    WitnessValues::from_map(std::collections::HashMap::from([(
        TemplateProgramWitness::witness_from_str(name),
        value,
    )]))
}

#[test]
#[cfg(feature = "serde")]
fn proof_of_work() {
    TestCase::program_file_with_unstable("./examples/proof_of_work.simf", UnstableFeatures::all())
        .with_witness_file("./examples/proof_of_work.wit")
        .assert_run_success();
}

#[test]
fn proof_of_work_needs_enough_work() {
    use crate::value::ValueConstructible;

    // The hash of nonce 0 starts with the byte 0xaf, which is above the target.
    TestCase::program_file_with_unstable("./examples/proof_of_work.simf", UnstableFeatures::all())
        .with_witness_values(single_witness("NONCE", Value::u64(0)))
        .assert_run_failure();
}

#[test]
#[cfg(feature = "serde")]
fn hash_lock_with_timeout_before_timeout() {
    TestCase::program_file_with_unstable(
        "./examples/hash_lock_with_timeout.simf",
        UnstableFeatures::all(),
    )
    .with_witness_file("./examples/hash_lock_with_timeout.wit")
    .assert_run_success();
}

#[test]
fn hash_lock_with_timeout_wrong_preimage() {
    use crate::num::U256;
    use crate::value::ValueConstructible;

    let wrong_preimage = || single_witness("PREIMAGE", Value::u256(U256::from(1u128)));

    // Before the timeout, the preimage must be right.
    TestCase::program_file_with_unstable(
        "./examples/hash_lock_with_timeout.simf",
        UnstableFeatures::all(),
    )
    .with_witness_values(wrong_preimage())
    .assert_run_failure();

    // After the timeout, `||` doesn't check the preimage.
    TestCase::program_file_with_unstable(
        "./examples/hash_lock_with_timeout.simf",
        UnstableFeatures::all(),
    )
    .with_lock_time(1000)
    .with_witness_values(wrong_preimage())
    .assert_run_success();
}

// ---------------------------------------------------------------------------
// Feature gating
// ---------------------------------------------------------------------------

#[test]
fn every_operator_needs_the_feature() {
    let operators = [
        "a == b", "a != b", "a < b", "a <= b", "a > b", "a >= b", "t & t", "t | t", "t ^ t",
        "t && t", "t || t", "!t",
    ];
    // Positions that the feature check must visit: a statement of `main`,
    // and an optional function before `main`.
    let positions: [fn(&str) -> (String, String); 8] = [
        |e| (String::new(), format!("let c: bool = {e};")),
        |e| {
            (
                String::new(),
                format!("let c: bool = match t {{ false => {e}, true => false, }};"),
            )
        },
        |e| {
            (
                String::new(),
                format!("let c: bool = match {e} {{ false => true, true => false, }};"),
            )
        },
        |e| (String::new(), format!("let c: bool = {{ {{ {e} }} }};")),
        |e| (String::new(), format!("let c: bool = id({e});")),
        |e| (String::new(), format!("let c: [bool; 1] = [{e}];")),
        |e| (String::new(), format!("let c: Option<bool> = Some({e});")),
        |e| {
            (
                format!("fn g(a: u8, b: u8, t: bool) -> bool {{\n    {e}\n}}\n\n"),
                "let c: bool = g(a, b, t);".to_string(),
            )
        },
    ];

    for operator in operators {
        for position in positions {
            let (function, statement) = position(operator);
            let text = format!(
                "fn id(c: bool) -> bool {{\n    c\n}}\n\n{function}fn main() {{\n    \
                 let a: u8 = 1;\n    let b: u8 = 2;\n    let t: bool = true;\n    {statement}\n}}\n"
            );
            if let Err(error) = TemplateAst::new_with_unstable(
                text.as_str(),
                &UnstableFeatures::all(),
                Box::new(ElementsJetHinter::new()),
            ) {
                panic!("Should compile with the feature:\n{text}\n{error}");
            }

            let error = match TemplateAst::new_with_unstable(
                text.as_str(),
                &UnstableFeatures::none(),
                Box::new(ElementsJetHinter::new()),
            ) {
                Ok(_) => panic!("Accepted without the feature:\n{text}"),
                Err(diagnostics) => diagnostics.to_string(),
            };
            assert!(
                error.contains("infix_operators"),
                "Rejection should name the feature for:\n{text}\nGot: {error}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Cost
// ---------------------------------------------------------------------------

/// The cost of `fn f(a: ty, b: ty) -> ret { body }` called on `(value, value)`,
/// in milliweight: the static bound over all branches, and the cost of the
/// branches that run, which is what a spending transaction pays.
fn function_cost(ty: &str, ret: &str, body: &str, value: &str) -> (i64, i64) {
    let text = format!(
        "fn f(a: {ty}, b: {ty}) -> {ret} {{\n    {body}\n}}\n\nfn main() {{\n    \
         let r: {ret} = f({value}, {value});\n}}\n"
    );
    let compiled = CompiledProgram::new_with_unstable(
        text.as_str(),
        &UnstableFeatures::all(),
        Arguments::default(),
        false,
        Box::new(ElementsJetHinter::new()),
    )
    .unwrap_or_else(|error| panic!("This program should compile:\n{text}\n{error}"));
    let env = dummy_env::dummy_with(elements::LockTime::ZERO, elements::Sequence::MAX, false);
    let milliweight = |cost: simplicity::Cost| cost.to_string().parse::<i64>().unwrap();
    let unpruned = compiled
        .satisfy(WitnessValues::default())
        .expect("no witnesses");
    let pruned = compiled
        .satisfy_with_env(WitnessValues::default(), Some(&env))
        .expect("no witnesses");
    (
        milliweight(unpruned.redeem().bounds().cost),
        milliweight(pruned.redeem().bounds().cost),
    )
}

/// Print the cost of each operator on each type, with equal operands.
///
/// Run with `cargo test --lib operator_costs -- --ignored --nocapture`.
#[test]
#[ignore = "prints a table of costs and doesn't check anything"]
fn operator_costs() {
    let u256_one = "0x0000000000000000000000000000000000000000000000000000000000000001";
    let types = [
        ("bool", "true"),
        ("u1", "1"),
        ("u2", "1"),
        ("u4", "1"),
        ("u8", "1"),
        ("u16", "1"),
        ("u32", "1"),
        ("u64", "1"),
        ("u128", "1"),
        ("u256", u256_one),
    ];

    let row = |label: &str, ty: &str, ret: &str, body: &str, value: &str, baseline: &str| {
        let (unpruned, pruned) = function_cost(ty, ret, body, value);
        let (base_unpruned, base_pruned) = function_cost(ty, ret, baseline, value);
        println!(
            "  {label:<44} {ty:<5} {:>7} {:>7}",
            unpruned - base_unpruned,
            pruned - base_pruned
        );
    };

    println!();
    println!("  operation (cost above `true` or `a`)          type   static     run");
    for (ty, value) in types {
        let is_bool = ty == "bool";
        for op in ["==", "!=", "<", "<=", ">", ">="] {
            if is_bool && !matches!(op, "==" | "!=") {
                continue;
            }
            row(
                &format!("a {op} b"),
                ty,
                "bool",
                &format!("a {op} b"),
                value,
                "true",
            );
        }
        for op in ["&", "|", "^"] {
            row(
                &format!("a {op} b"),
                ty,
                ty,
                &format!("a {op} b"),
                value,
                "a",
            );
        }
        if is_bool {
            for e in ["a && b", "a || b", "!a"] {
                row(e, ty, "bool", e, value, "true");
            }
        }
    }

    println!();
}
