use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
};

use nom::{
  branch::alt,
  combinator::{all_consuming, map},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};

use crate::{
  ast::{meta, Type},
  CodegenContext, Expr, LocalContext, ParseContext, Statement,
};

/// The body of a macro.
#[derive(Debug, Clone)]
pub enum MacroBody {
  /// A statement, e.g.
  ///
  /// ```c
  /// #define BLOCK do { \
  ///   a += b; \
  /// } while (0)
  /// ```
  ///
  /// or
  ///
  /// ```c
  /// #define STMT a += b;
  /// ```
  Statement(Statement),
  /// An expression, e.g.
  ///
  /// ```c
  /// #define EXPR a + b
  /// ```
  Expr(Expr),
}

impl MacroBody {
  pub(crate) fn parse<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, _) = meta(tokens)?;

    if tokens.is_empty() {
      return Ok((tokens, Self::Statement(Statement::Block(vec![]))))
    }

    let (tokens, body) = alt((
      all_consuming(map(|tokens| Expr::parse(tokens, ctx), Self::Expr)),
      all_consuming(map(|tokens| Statement::parse(tokens, ctx), Self::Statement)),
    ))(tokens)?;

    Ok((tokens, body))
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::Statement(stmt) => stmt.finish(ctx),
      Self::Expr(expr) => expr.finish(ctx),
    }
  }
}
