use crate::driver::MAIN_MODULE;
use crate::error::{DiagnosticManager, Error};
use crate::parse::{
    Expression, ExpressionInner, ParseFromStr, ParseFromStrWithErrors, Program,
    SingleExpressionInner,
};
use crate::UnstableFeatures;

/// Render the operator structure of an expression with every operator node
/// parenthesized, and everything else as displayed.
fn shape(expression: &Expression) -> String {
    match expression.inner() {
        ExpressionInner::Single(single) => match single.inner() {
            SingleExpressionInner::BinaryOp(binary_op) => format!(
                "({} {} {})",
                shape(binary_op.lhs()),
                binary_op.op(),
                shape(binary_op.rhs())
            ),
            SingleExpressionInner::LogicalNot(logical_not) => {
                format!("(!{})", shape(logical_not.operand()))
            }
            _ => expression.to_string(),
        },
        ExpressionInner::Block(..) => expression.to_string(),
    }
}

fn parse(input: &str) -> Expression {
    Expression::parse_from_str(input)
        .unwrap_or_else(|error| panic!("{input:?} should parse, got: {error:?}"))
}

/// The grammar error that parsing `input` reports first.
fn grammar_error(input: &str) -> String {
    let error =
        Expression::parse_from_str(input).expect_err(&format!("{input:?} should be rejected"));
    match error.error() {
        Error::Grammar { msg } => msg.clone(),
        other => panic!("{input:?} should give a grammar error, got: {other:?}"),
    }
}

#[test]
fn operators_bind_with_rust_precedence() {
    let cases = [
        ("a == b", "(a == b)"),
        ("a != b", "(a != b)"),
        ("a < b", "(a < b)"),
        ("a <= b", "(a <= b)"),
        ("a > b", "(a > b)"),
        ("a >= b", "(a >= b)"),
        ("a>=b", "(a >= b)"),
        ("a == b && c == d", "((a == b) && (c == d))"),
        ("a < b || c >= d", "((a < b) || (c >= d))"),
        ("a || b && c", "(a || (b && c))"),
        ("a && b || c", "((a && b) || c)"),
        ("a || b || c", "((a || b) || c)"),
        ("a && b && c", "((a && b) && c)"),
        // As in Rust and unlike C, bitwise operators bind tighter than comparisons.
        ("a & b == c", "((a & b) == c)"),
        ("a == b | c", "(a == (b | c))"),
        ("a | b ^ c & d", "(a | (b ^ (c & d)))"),
        ("a & b ^ c | d", "(((a & b) ^ c) | d)"),
        ("a & b & c", "((a & b) & c)"),
        ("!a", "(!a)"),
        ("!!a", "(!(!a))"),
        ("!a == b", "((!a) == b)"),
        ("!a && !b", "((!a) && (!b))"),
        ("!(a == b)", "(!(a == b))"),
        ("(a || b) && c", "((a || b) && c)"),
        ("jet::eq_8(a, b) == c", "(jet::eq_8(a, b) == c)"),
        ("<u8>::into(a) < b", "(<u8>::into(a) < b)"),
        ("a < <u8>::into(b)", "(a < <u8>::into(b))"),
        ("Some(a == b)", "Some(a == b)"),
        ("(a == b, c != d)", "(a == b, c != d)"),
    ];

    for (input, expected) in cases {
        assert_eq!(shape(&parse(input)), expected, "for input {input:?}");
    }
}

#[test]
fn operator_expressions_display_as_they_parse() {
    for input in [
        "a == b && c == d",
        "a || b && c",
        "(a || b) && c",
        "a & b ^ c | d",
        "!a == !b",
        "!(a && b)",
        "a >= b",
        "match a < b { false => c, true => d, }",
    ] {
        let expression = parse(input);
        let displayed = expression.to_string();
        assert_eq!(
            parse(&displayed),
            expression,
            "{input:?} displays as {displayed:?}, which parses differently"
        );
    }
}

#[test]
fn operator_spans_cover_operands() {
    let expression = parse("a == bb && !c");
    let ExpressionInner::Single(single) = expression.inner() else {
        panic!("expected a single expression");
    };
    let SingleExpressionInner::BinaryOp(and) = single.inner() else {
        panic!("expected `&&` at the top");
    };
    assert_eq!((and.span().start, and.span().end), (0, 13));
    assert_eq!((and.lhs().span().start, and.lhs().span().end), (0, 7));
    assert_eq!((and.rhs().span().start, and.rhs().span().end), (11, 13));
}

#[test]
fn comparisons_cannot_be_chained() {
    for input in ["a < b < c", "a == b == c", "a == b != c", "a <= b >= c"] {
        let msg = grammar_error(input);
        assert!(
            msg.contains("cannot be chained"),
            "unexpected error for {input:?}: {msg}"
        );
    }
}

#[test]
fn spaced_greater_or_equal_is_rejected() {
    let msg = grammar_error("a > = b");
    assert!(msg.contains("`>=`"), "unexpected error: {msg}");
}

#[test]
fn type_closing_angle_before_assignment_still_parses() {
    let input = "fn main() {\n    let x: Option<u8>= None;\n    let y: Either<u8, u16>=Left(1);\n}";
    assert!(
        Program::parse_from_str(input).is_ok(),
        "`>=` right after a type must still close the type"
    );
}

#[test]
fn operators_need_unstable_feature() {
    for input in [
        "fn main() {\n    assert!(a == b);\n}",
        "fn main() {\n    assert!(!a);\n}",
    ] {
        let mut diagnostics = DiagnosticManager::new();
        let program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            &UnstableFeatures::none(),
            &mut diagnostics,
        );
        let error = diagnostics.to_string();
        assert!(program.is_none(), "{input:?} must be rejected without -Z");
        assert!(
            error.contains("infix_operators") && error.contains("-Z"),
            "rejection should name the feature and suggest -Z, got:\n{error}"
        );

        let mut diagnostics = DiagnosticManager::new();
        let program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            &UnstableFeatures::all(),
            &mut diagnostics,
        );
        assert!(
            program.is_some(),
            "{input:?} must parse with all features enabled:\n{diagnostics}"
        );
    }
}

#[test]
fn syntax_errors_near_comparisons_are_reported() {
    for input in [
        // An unmatched `<` inside a call whose arguments fail to parse.
        "fn main() {\n    assert!(jet::eq_8(a < , b));\n}",
        // A `<` and a later `>` around a syntax error.
        "fn main() {\n    let x: bool = a < b;\n    let y u8 = 1;\n    let z: bool = c > d;\n}",
        // A broken block between two functions that use comparisons.
        "fn f(a: u8) -> bool {\n    a < 3\n}\nfn main() {\n    let = ;\n}\nfn g(a: u8) -> bool {\n    a > 3\n}",
    ] {
        let mut diagnostics = DiagnosticManager::new();
        let program = Program::parse_from_str_with_errors(
            MAIN_MODULE,
            input,
            &UnstableFeatures::all(),
            &mut diagnostics,
        );
        assert!(program.is_none(), "{input:?} must be rejected");
        assert!(
            diagnostics.has_errors(),
            "{input:?} must report an error"
        );
    }
}
