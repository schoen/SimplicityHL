//! Type checking of operators.
//!
//! Each operator is rewritten into an equivalent parse-tree expression that the
//! rest of the checker already handles: a jet call, a type cast, or a `match`
//! on a boolean. The rewritten expression is then checked in place of the
//! operator, so the abstract syntax tree doesn't contain any operator nodes.

use crate::error::{Error, WithSpan};
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
        InfixOp::Eq | InfixOp::Ne | InfixOp::Lt | InfixOp::Le | InfixOp::Gt | InfixOp::Ge => {
            Err(Error::Grammar {
                msg: "Comparison operators are not supported yet".to_string(),
            })
            .with_span(from)?
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
    span: crate::error::Span,
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
        let to_u1 = |operand: parse::Expression| {
            parse::SingleExpression::type_cast(AliasedType::boolean(), operand, span)
                .into_expression()
        };
        let jet = parse::SingleExpression::jet_call(
            &format!("{name}_1"),
            vec![to_u1(lhs), to_u1(rhs)],
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
