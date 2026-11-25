use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{
    any, choice, just, nested_delimiters, one_of, recursive, skip_then_retry_until,
};
use chumsky::{select, IterParser, Parser};
use either::Either;

use crate::error::{Diagnostic, Error, Span};
use crate::lexer::Token;
use crate::str::Identifier;
use crate::TemplateProgramWitness;

use super::super::{
    BinaryOp, Call, EnumConstruction, Expression, ExpressionInner, InfixOp, Not,
    SingleExpression, SingleExpressionInner, Statement,
};
use super::matching::match_expr_parser;
use super::{delimited_with_recovery, ChumskyParse, ParseError};

/// Split a parsed block body into its statements and its optional final expression.
///
/// Each element arrives paired with the `;` that followed it, if any. Only the last
/// element may omit its `;`, and only when it is an expression rather than an
/// assignment: that element is the block's final expression. Every other missing `;`
/// is reported, and the element is kept as a statement so that analysis of the rest
/// of the block still happens.
fn split_block_body(
    elements: Vec<(Statement, Option<Token<'_>>)>,
    emit: &mut chumsky::input::Emitter<Diagnostic>,
) -> (Arc<[Statement]>, Option<Arc<Expression>>) {
    let count = elements.len();
    let mut statements = Vec::with_capacity(count);
    let mut final_expr = None;

    for (index, (statement, semi)) in elements.into_iter().enumerate() {
        if semi.is_some() {
            statements.push(statement);
            continue;
        }

        match statement {
            // A trailing expression without `;` is the block's value.
            Statement::Expression(expression) if index + 1 == count => {
                final_expr = Some(Arc::new(expression));
            }
            statement => {
                emit.emit(
                    Error::Grammar {
                        msg: "Expected `;` after statement".to_string(),
                    }
                    .with_span(*statement.span()),
                );
                statements.push(statement);
            }
        }
    }

    (Arc::from(statements), final_expr)
}

impl ChumskyParse for Expression {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|expr| {
            let block = {
                // A block body is a run of elements, each of which is a statement
                // followed by `;`, except that the last one may drop the `;` and
                // become the block's final expression.
                let element = Statement::parser(expr.clone()).then(just(Token::Semi).or_not());

                // Not `<` and `>`, which are also comparison operators.
                let block_recovery = nested_delimiters(
                    Token::LBrace,
                    Token::RBrace,
                    [
                        (Token::LParen, Token::RParen),
                        (Token::LBracket, Token::RBracket),
                    ],
                    |span| Expression::empty(span).inner().clone(),
                );

                let body = element
                    .repeated()
                    .collect::<Vec<_>>()
                    .validate(|elements, _, emit| split_block_body(elements, emit))
                    .recover_with(skip_then_retry_until(
                        block_recovery.ignored().or(any().ignored()),
                        one_of([Token::Semi, Token::RParen, Token::RBracket, Token::RBrace])
                            .ignored(),
                    ));

                delimited_with_recovery(body, Token::LBrace, Token::RBrace, |_| {
                    (Arc::from(Vec::new()), None)
                })
                .map(|(stmts, end_expr)| ExpressionInner::Block(stmts, end_expr))
            };

            let single = SingleExpression::parser(expr.clone()).map(ExpressionInner::Single);

            choice((block, single))
                .map_with(|inner, e| Expression {
                    inner,
                    span: e.span(),
                })
                .labelled("expression")
        })
    }
}

impl SingleExpression {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let wrapper = |name: &'static str| {
            select! { Token::Ident(i) if i == name => i }.ignore_then(
                expr.clone()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
        };

        let left =
            wrapper("Left").map(|e| SingleExpressionInner::Either(Either::Left(Arc::new(e))));

        let right =
            wrapper("Right").map(|e| SingleExpressionInner::Either(Either::Right(Arc::new(e))));

        let some = wrapper("Some").map(|e| SingleExpressionInner::Option(Some(Arc::new(e))));

        // Bare `None` is the option literal only when no `::` follows:
        // `None::A` is a construction of an enum aliased as `None`, and
        // must fall through to the enum-construction alternative.
        let none = select! { Token::Ident("None") => SingleExpressionInner::Option(None) }
            .then_ignore(just(Token::DoubleColon).not().rewind());

        let boolean = select! { Token::Bool(b) => SingleExpressionInner::Boolean(b) };

        let comma_separated = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let array = delimited_with_recovery(
            comma_separated.clone(),
            Token::LBracket,
            Token::RBracket,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Array(Arc::from(es)));

        let list = just(Token::Macro("list!"))
            .ignore_then(delimited_with_recovery(
                comma_separated.clone(),
                Token::LBracket,
                Token::RBracket,
                |_| Vec::new(),
            ))
            .map(|es| SingleExpressionInner::List(Arc::from(es)));

        let tuple = delimited_with_recovery(
            comma_separated.clone(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Tuple(Arc::from(es)));

        let literal = select! {
            Token::DecLiteral(s) => SingleExpressionInner::Decimal(s),
            Token::HexLiteral(s) => SingleExpressionInner::Hexadecimal(s),
            Token::BinLiteral(s) => SingleExpressionInner::Binary(s),
            Token::Witness(s) => SingleExpressionInner::Witness(TemplateProgramWitness::witness_from_str(s)),
            Token::Param(s) => SingleExpressionInner::Parameter(TemplateProgramWitness::parameter_from_str(s)),
        };

        // Enum variant construction: `Path::To::Enum::Variant(args..)`.
        // At least one `::` distinguishes the path from variables and calls.
        // The built-in wrappers (Left, Some, ...) require `(` directly after
        // their name, so they never reach this alternative.
        let enum_construction = Identifier::parser()
            .separated_by(just(Token::DoubleColon))
            .at_least(2)
            .collect::<Vec<Identifier>>()
            .then(
                comma_separated
                    .clone()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .map_with(|(mut segments, args), e| {
                let variant = segments.pop().expect("the parser requires two segments");
                EnumConstruction {
                    enum_path: Arc::from(segments),
                    variant,
                    args: Arc::from(args.unwrap_or_default()),
                    span: e.span(),
                }
            })
            .map(SingleExpressionInner::EnumConstruction);

        let call = Call::parser(expr.clone()).map(SingleExpressionInner::Call);

        let match_expr = match_expr_parser(expr.clone());

        let variable = Identifier::parser().map(SingleExpressionInner::Variable);

        // Expression delimeted by parentheses
        let expression = expr
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|es| SingleExpressionInner::Expression(Arc::from(es)));

        let atom = choice((
            left,
            right,
            some,
            none,
            boolean,
            match_expr,
            expression,
            list,
            array,
            tuple,
            enum_construction,
            call,
            literal,
            variable,
        ))
        .map_with(|inner, e| Self {
            inner,
            span: e.span(),
        })
        .boxed();

        // Operators, from the tightest binding to the loosest, as in Rust:
        // `!`, `&`, `^`, `|`, comparisons, `&&`, `||`. Each level is boxed, because
        // it refers to the level below twice and the parser's type would otherwise
        // double in size at every level.

        let not = just(Token::Bang)
            .map_with(|_, e| -> Span { e.span() })
            .repeated()
            .foldr(atom, |bang, operand| {
                let span = join_spans(bang, operand.span);
                Self {
                    inner: SingleExpressionInner::Not(Not {
                        operand: Arc::new(operand.into_expression()),
                        span,
                    }),
                    span,
                }
            })
            .boxed();

        let bit_and = binary_level(not, just(Token::Amp).to(InfixOp::BitAnd)).boxed();
        let bit_xor = binary_level(bit_and, just(Token::Caret).to(InfixOp::BitXor)).boxed();
        let bit_or = binary_level(bit_xor, just(Token::Pipe).to(InfixOp::BitOr)).boxed();

        // The lexer has no `>=` token, because in `let x: Option<u8>= None;` the `>`
        // closes a type. In operator position, `>` directly followed by `=` is `>=`.
        let ge = just(Token::RAngle)
            .map_with(|_, e| -> Span { e.span() })
            .then(just(Token::Eq).map_with(|_, e| -> Span { e.span() }))
            .validate(|(gt, eq), _, emit| {
                if gt.end != eq.start {
                    emit.emit(
                        Error::Grammar {
                            msg: "Expected `>=`, found `> =`".to_string(),
                        }
                        .with_span(join_spans(gt, eq))
                        .with_help("remove the space between `>` and `=`"),
                    );
                }
                InfixOp::Ge
            });

        let comparison_op = choice((
            just(Token::EqEq).to(InfixOp::Eq),
            just(Token::BangEq).to(InfixOp::Ne),
            just(Token::LtEq).to(InfixOp::Le),
            just(Token::LAngle).to(InfixOp::Lt),
            ge,
            just(Token::RAngle).to(InfixOp::Gt),
        ));

        // Comparisons don't associate: `a < b < c` is an error, as in Rust.
        let comparison = bit_or
            .clone()
            .then(comparison_op.then(bit_or).repeated().collect::<Vec<_>>())
            .validate(|(first, rest), _, emit| {
                if rest.len() > 1 {
                    let last = rest.last().expect("rest has two elements").1.span;
                    emit.emit(
                        Error::Grammar {
                            msg: "Comparison operators cannot be chained".to_string(),
                        }
                        .with_span(join_spans(first.span, last))
                        .with_help("use parentheses, or `&&` between two comparisons"),
                    );
                }
                rest.into_iter()
                    .fold(first, |lhs, (op, rhs)| Self::binary(lhs, op, rhs))
            })
            .boxed();

        let and = binary_level(comparison, just(Token::AmpAmp).to(InfixOp::And)).boxed();
        binary_level(and, just(Token::PipePipe).to(InfixOp::Or)).boxed()
    }

    /// Build the infix operator expression `lhs op rhs`.
    fn binary(lhs: Self, op: InfixOp, rhs: Self) -> Self {
        let span = join_spans(lhs.span, rhs.span);
        Self {
            inner: SingleExpressionInner::BinaryOp(BinaryOp {
                op,
                lhs: Arc::new(lhs.into_expression()),
                rhs: Arc::new(rhs.into_expression()),
                span,
            }),
            span,
        }
    }
}

/// The smallest span that covers both spans.
///
/// Spans from error recovery need not be in source order, so this doesn't
/// assume that `first` starts before `second`.
fn join_spans(first: Span, second: Span) -> Span {
    Span::new(
        first.file_id,
        first.start.min(second.start)..first.end.max(second.end),
    )
}

/// One left-associative level of infix operators: `operand (op operand)*`.
fn binary_level<'tokens, 'src: 'tokens, I, P, O>(
    operand: P,
    op: O,
) -> impl Parser<'tokens, I, SingleExpression, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    P: Parser<'tokens, I, SingleExpression, ParseError<'src>> + Clone,
    O: Parser<'tokens, I, InfixOp, ParseError<'src>> + Clone,
{
    operand
        .clone()
        .foldl(op.then(operand).repeated(), |lhs, (op, rhs)| {
            SingleExpression::binary(lhs, op, rhs)
        })
}
