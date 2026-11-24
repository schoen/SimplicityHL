//! Type checking of operators.
//!
//! Each operator is rewritten into an equivalent parse-tree expression that the
//! rest of the checker already handles: a jet call, a type cast, or a `match`
//! on a boolean. The rewritten expression is then checked in place of the
//! operator, so the abstract syntax tree doesn't contain any operator nodes.

use crate::error::{Error, Span, WithSpan};
use crate::jet::target_type;
use crate::parse::{self, InfixOp};
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

    let width = match ty.as_integer() {
        Some(UIntType::U1) => 1,
        Some(UIntType::U8) => 8,
        Some(UIntType::U16) => 16,
        Some(UIntType::U32) => 32,
        Some(UIntType::U64) => 64,
        _ => {
            return Err(Error::OperatorUnsupportedType {
                op: op.as_str(),
                ty: ty.clone(),
            })
        }
    };
    Ok(parse::SingleExpression::jet_call(
        &format!("{name}_{width}"),
        vec![lhs, rhs],
        span,
    ))
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

    // Booleans compare as `u1`, which has the same representation.
    let (width, lhs, rhs) = if operand_ty.is_boolean() {
        (1, bool_to_u1(lhs, span), bool_to_u1(rhs, span))
    } else {
        let width = match operand_ty.as_integer() {
            Some(UIntType::U1) => 1,
            Some(UIntType::U8) => 8,
            Some(UIntType::U16) => 16,
            Some(UIntType::U32) => 32,
            Some(UIntType::U64) => 64,
            Some(UIntType::U256) => 256,
            _ => return Err(unsupported()),
        };
        (width, lhs, rhs)
    };

    // `eq_N` exists for every width above; `lt_N` and `le_N` only for these.
    let is_ordering = !matches!(op, InfixOp::Eq | InfixOp::Ne);
    if is_ordering && !matches!(width, 8 | 16 | 32 | 64) {
        return Err(unsupported());
    }

    let jet = |name: &str, args| {
        parse::SingleExpression::jet_call(&format!("{name}_{width}"), args, span)
    };
    let boolean = |value| parse::SingleExpression::boolean(value, span).into_expression();

    Ok(match op {
        InfixOp::Eq => jet("eq", vec![lhs, rhs]),
        InfixOp::Ne => parse::SingleExpression::bool_match(
            jet("eq", vec![lhs, rhs]).into_expression(),
            boolean(true),
            boolean(false),
            span,
        ),
        InfixOp::Lt => jet("lt", vec![lhs, rhs]),
        InfixOp::Le => jet("le", vec![lhs, rhs]),
        // There are no greater-than jets, so `a > b` is `b < a`. This evaluates
        // `b` before `a`. Evaluation doesn't have side effects other than
        // failing, so the order only decides which failure is reported when
        // both operands fail.
        InfixOp::Gt => jet("lt", vec![rhs, lhs]),
        InfixOp::Ge => jet("le", vec![rhs, lhs]),
        _ => unreachable!("`{op}` is not a comparison operator"),
    })
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
