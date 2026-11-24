//! Type checking of operators.
//!
//! Each operator is rewritten into an equivalent parse-tree expression that the
//! rest of the checker already handles: a jet call, a type cast, or a `match`
//! on a boolean. The rewritten expression is then checked in place of the
//! operator, so the abstract syntax tree doesn't contain any operator nodes.

use crate::error::{Error, Span, WithSpan};
use crate::jet::target_type;
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
    let boolean = |value| parse::SingleExpression::boolean(value, span).into_expression();

    let rewritten = match from.op() {
        // `a && b` is `match a { false => false, true => b }`, which doesn't
        // evaluate `b` when `a` is false.
        InfixOp::And => {
            expect_boolean(ty).with_span(from)?;
            parse::SingleExpression::bool_match(lhs, boolean(false), rhs, span)
        }
        // `a || b` is `match a { false => b, true => true }`, which doesn't
        // evaluate `b` when `a` is true.
        InfixOp::Or => {
            expect_boolean(ty).with_span(from)?;
            parse::SingleExpression::bool_match(lhs, rhs, boolean(true), span)
        }
        op @ (InfixOp::BitAnd | InfixOp::BitOr | InfixOp::BitXor) => {
            bitwise(op, lhs, rhs, ty, span).with_span(from)?
        }
        op
        @ (InfixOp::Eq | InfixOp::Ne | InfixOp::Lt | InfixOp::Le | InfixOp::Gt | InfixOp::Ge) => {
            expect_boolean(ty).with_span(from)?;
            let known: &Scope = scope;
            let operand_ty = operand_type(&lhs, known)
                .or_else(|| operand_type(&rhs, known))
                .ok_or(Error::OperatorOperandTypeUnknown { op: op.as_str() })
                .with_span(from)?;
            comparison(op, lhs, rhs, &operand_ty, span).with_span(from)?
        }
    };

    analyze_rewritten(&rewritten, ty, scope)
}

/// Analyze `!operand`, which must be of type `ty`.
///
/// `!a` is `match a { false => true, true => false }`.
pub(super) fn analyze_not(
    from: &parse::LogicalNot,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<SingleExpressionInner, Failure> {
    expect_boolean(ty).with_span(from)?;

    let span = *from.span();
    let boolean = |value| parse::SingleExpression::boolean(value, span).into_expression();
    let rewritten = parse::SingleExpression::bool_match(
        from.operand().clone(),
        boolean(true),
        boolean(false),
        span,
    );

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

/// Rewrite a bitwise operator into the jet for the width of `ty`, which is the
/// type of both operands and of the result.
fn bitwise(
    op: InfixOp,
    lhs: parse::Expression,
    rhs: parse::Expression,
    ty: &ResolvedType,
    span: Span,
) -> Result<parse::SingleExpression, Error> {
    let name = match op {
        InfixOp::BitAnd => "and",
        InfixOp::BitOr => "or",
        InfixOp::BitXor => "xor",
        _ => unreachable!("`{op}` is not a bitwise operator"),
    };

    // A boolean has the same representation as a `u1`, so the `u1` jet works
    // on booleans after a cast in each direction:
    // `<u1>::into(jet::and_1(<bool>::into(a), <bool>::into(b)))`.
    if ty.is_boolean() {
        let jet = parse::SingleExpression::jet_call(
            &format!("{name}_1"),
            vec![bool_to_u1(lhs, span), bool_to_u1(rhs, span)],
            span,
        );
        return Ok(parse::SingleExpression::type_cast(
            AliasedType::from(UIntType::U1),
            jet.into_expression(),
            span,
        ));
    }

    // There are no jets for `u2` and `u4`: use the `u8` jet on zero-extended
    // operands and keep the low bits of the result.
    if let Some(small @ (UIntType::U2 | UIntType::U4)) = ty.as_integer() {
        let small = small_width(small);
        let wide = parse::SingleExpression::jet_call(
            &format!("{name}_8"),
            vec![
                extend_to_u8(lhs, small, span),
                extend_to_u8(rhs, small, span),
            ],
            span,
        );
        return Ok(parse::SingleExpression::jet_call(
            &format!("rightmost_8_{small}"),
            vec![wide.into_expression()],
            span,
        ));
    }

    let width = match ty.as_integer() {
        Some(UIntType::U1) => 1,
        Some(UIntType::U8) => 8,
        Some(UIntType::U16) => 16,
        Some(UIntType::U32) => 32,
        Some(UIntType::U64) => 64,
        Some(UIntType::U128) => 128,
        Some(UIntType::U256) => 256,
        _ => {
            return Err(Error::OperatorUnsupportedType {
                op: op.as_str(),
                ty: ty.clone(),
            })
        }
    };
    Ok(parse::SingleExpression::from_expression(bitwise_jets(
        name, lhs, rhs, width, span,
    )))
}

/// Apply the bitwise jet `name` to operands of the given width. Above 64 bits,
/// where there are no jets, apply it to the high halves and to the low halves.
fn bitwise_jets(
    name: &str,
    lhs: parse::Expression,
    rhs: parse::Expression,
    width: usize,
    span: Span,
) -> parse::Expression {
    if width <= 64 {
        return parse::SingleExpression::jet_call(&format!("{name}_{width}"), vec![lhs, rhs], span)
            .into_expression();
    }

    let half = width / 2;
    let high = bitwise_jets(
        name,
        variable(LHS_HIGH, span),
        variable(RHS_HIGH, span),
        half,
        span,
    );
    let low = bitwise_jets(
        name,
        variable(LHS_LOW, span),
        variable(RHS_LOW, span),
        half,
        span,
    );
    let halves = parse::SingleExpression::tuple(vec![high, low], span).into_expression();
    let joined =
        parse::SingleExpression::type_cast(pair_type(uint(half)), halves, span).into_expression();
    with_halves(lhs, rhs, width, joined, span)
}

/// Rewrite a comparison of two operands of type `operand_ty` into a jet call.
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

    let is_ordering = !matches!(op, InfixOp::Eq | InfixOp::Ne);

    let (width, lhs, rhs) = if operand_ty.is_boolean() {
        // Booleans compare as `u1`, which has the same representation.
        if is_ordering {
            return Err(unsupported());
        }
        (1, bool_to_u1(lhs, span), bool_to_u1(rhs, span))
    } else {
        match operand_ty.as_integer() {
            // There are no jets for `u2` and `u4`, nor ordering jets for `u1`:
            // compare the operands zero-extended to `u8`.
            Some(small @ (UIntType::U2 | UIntType::U4)) => {
                let small = small_width(small);
                (
                    8,
                    extend_to_u8(lhs, small, span),
                    extend_to_u8(rhs, small, span),
                )
            }
            Some(UIntType::U1) if is_ordering => {
                (8, extend_to_u8(lhs, 1, span), extend_to_u8(rhs, 1, span))
            }
            Some(UIntType::U1) => (1, lhs, rhs),
            Some(UIntType::U8) => (8, lhs, rhs),
            Some(UIntType::U16) => (16, lhs, rhs),
            Some(UIntType::U32) => (32, lhs, rhs),
            Some(UIntType::U64) => (64, lhs, rhs),
            Some(UIntType::U128) => (128, lhs, rhs),
            Some(UIntType::U256) => (256, lhs, rhs),
            _ => return Err(unsupported()),
        }
    };

    let compare = |name, lhs, rhs| comparison_jets(name, lhs, rhs, width, span);
    let boolean = |value| parse::SingleExpression::boolean(value, span).into_expression();

    let rewritten = match op {
        InfixOp::Eq => compare("eq", lhs, rhs),
        InfixOp::Ne => parse::SingleExpression::bool_match(
            compare("eq", lhs, rhs),
            boolean(true),
            boolean(false),
            span,
        )
        .into_expression(),
        InfixOp::Lt => compare("lt", lhs, rhs),
        InfixOp::Le => compare("le", lhs, rhs),
        // There are no greater-than jets, so `a > b` is `b < a`. This evaluates
        // `b` before `a`. Evaluation doesn't have side effects other than
        // failing, so the order only decides which failure is reported when
        // both operands fail.
        InfixOp::Gt => compare("lt", rhs, lhs),
        InfixOp::Ge => compare("le", rhs, lhs),
        _ => unreachable!("`{op}` is not a comparison operator"),
    };
    Ok(parse::SingleExpression::from_expression(rewritten))
}

/// Compare operands of the given width with the jet `name`, which is `eq`, `lt`
/// or `le`. Where that jet doesn't exist for the width, compare the halves:
///
/// - `a == b` is `a_high == b_high && a_low == b_low`.
/// - `a < b` is `a_high < b_high || (a_high == b_high && a_low < b_low)`, and
///   `a <= b` is the same with `a_low <= b_low`.
fn comparison_jets(
    name: &'static str,
    lhs: parse::Expression,
    rhs: parse::Expression,
    width: usize,
    span: Span,
) -> parse::Expression {
    let has_jet = match name {
        "eq" => matches!(width, 1 | 8 | 16 | 32 | 64 | 256),
        _ => matches!(width, 8 | 16 | 32 | 64),
    };
    if has_jet {
        return parse::SingleExpression::jet_call(&format!("{name}_{width}"), vec![lhs, rhs], span)
            .into_expression();
    }

    let half = width / 2;
    let high = |name| {
        comparison_jets(
            name,
            variable(LHS_HIGH, span),
            variable(RHS_HIGH, span),
            half,
            span,
        )
    };
    let low = |name| {
        comparison_jets(
            name,
            variable(LHS_LOW, span),
            variable(RHS_LOW, span),
            half,
            span,
        )
    };
    let boolean = |value| parse::SingleExpression::boolean(value, span).into_expression();

    let result = if name == "eq" {
        parse::SingleExpression::bool_match(high("eq"), boolean(false), low("eq"), span)
    } else {
        let high_equal_then_low =
            parse::SingleExpression::bool_match(high("eq"), boolean(false), low(name), span)
                .into_expression();
        parse::SingleExpression::bool_match(high("lt"), high_equal_then_low, boolean(true), span)
    };
    with_halves(lhs, rhs, width, result.into_expression(), span)
}

/// Names of the halves of the operands inside [`with_halves`].
const LHS_HIGH: &str = "lhs_high";
const LHS_LOW: &str = "lhs_low";
const RHS_HIGH: &str = "rhs_high";
const RHS_LOW: &str = "rhs_low";

/// Build a block that splits both operands, of the given width, into halves
/// named [`LHS_HIGH`], [`LHS_LOW`], [`RHS_HIGH`] and [`RHS_LOW`], and ends in
/// `body`:
///
/// ```text
/// {
///     let ((lhs_high, lhs_low), (rhs_high, rhs_low)): ((u64, u64), (u64, u64)) =
///         <(u128, u128)>::into((lhs, rhs));
///     body
/// }
/// ```
///
/// Both operands are evaluated before any name is bound, and `body` refers
/// only to the halves, so the names can't capture any variable of the program.
fn with_halves(
    lhs: parse::Expression,
    rhs: parse::Expression,
    width: usize,
    body: parse::Expression,
    span: Span,
) -> parse::Expression {
    let name = |name| Pattern::Identifier(crate::str::Identifier::from_str_unchecked(name));
    let pattern = Pattern::tuple([
        Pattern::tuple([name(LHS_HIGH), name(LHS_LOW)]),
        Pattern::tuple([name(RHS_HIGH), name(RHS_LOW)]),
    ]);
    let halves_ty = AliasedType::tuple([pair_type(uint(width / 2)), pair_type(uint(width / 2))]);
    let operands = parse::SingleExpression::tuple(vec![lhs, rhs], span).into_expression();
    let split = parse::SingleExpression::type_cast(pair_type(uint(width)), operands, span)
        .into_expression();
    let statement = parse::SingleExpression::assignment(pattern, halves_ty, split, span);
    parse::SingleExpression::block(vec![statement], body, span)
}

/// The type `(ty, ty)`.
fn pair_type(ty: UIntType) -> AliasedType {
    AliasedType::tuple([AliasedType::from(ty), AliasedType::from(ty)])
}

/// The unsigned integer type of the given width.
fn uint(width: usize) -> UIntType {
    match width {
        1 => UIntType::U1,
        2 => UIntType::U2,
        4 => UIntType::U4,
        8 => UIntType::U8,
        16 => UIntType::U16,
        32 => UIntType::U32,
        64 => UIntType::U64,
        128 => UIntType::U128,
        256 => UIntType::U256,
        _ => unreachable!("there is no `u{width}`"),
    }
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
        S::Boolean(_) | S::LogicalNot(_) => Some(ResolvedType::boolean()),
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

/// The width of `u1`, `u2` or `u4`.
fn small_width(ty: UIntType) -> usize {
    match ty {
        UIntType::U1 => 1,
        UIntType::U2 => 2,
        UIntType::U4 => 4,
        _ => unreachable!("`{ty}` is not narrower than `u8`"),
    }
}

/// Zero-extend a `u1`, `u2` or `u4` operand of the given width to `u8`, one
/// doubling at a time. `<(u4, u4)>::into((0, x))` is the `u8` whose high half
/// is zero and whose low half is `x`.
fn extend_to_u8(operand: parse::Expression, width: usize, span: Span) -> parse::Expression {
    let mut extended = operand;
    let mut width = width;
    while width < 8 {
        let half = AliasedType::from(match width {
            1 => UIntType::U1,
            2 => UIntType::U2,
            4 => UIntType::U4,
            _ => unreachable!("width {width} is not 1, 2 or 4"),
        });
        let zero = parse::SingleExpression::decimal("0", span).into_expression();
        let pair = parse::SingleExpression::tuple(vec![zero, extended], span).into_expression();
        extended = parse::SingleExpression::type_cast(
            AliasedType::tuple([half.clone(), half]),
            pair,
            span,
        )
        .into_expression();
        width *= 2;
    }
    extended
}
