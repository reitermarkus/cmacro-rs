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
  CodegenContext, Expr, LocalContext, Statement,
};

/// The body of a macro.
///
/// Can either be a block/statement, e.g.
///
/// ```c
/// #define BLOCK do { \
///   a += b; \
/// } while (0)
/// ```
///
/// or an expression, e.g.
///
/// ```c
/// #define EXPR a + b
/// ```
#[derive(Debug)]
pub enum MacroBody {
  Block(Statement),
  Expr(Expr),
}

impl MacroBody {
  pub fn parse<'i, I, C>(input: &'i [I]) -> IResult<&'i [I], Self>
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
    let (input, _) = meta(input)?;

    if input.is_empty() {
      return Ok((input, MacroBody::Block(Statement::Block(vec![]))))
    }

    let (input, body) = alt((
      all_consuming(map(Expr::parse, MacroBody::Expr)),
      all_consuming(map(Statement::parse, MacroBody::Block)),
    ))(input)?;

    Ok((input, body))
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    match self {
      Self::Block(stmt) => stmt.finish(ctx),
      Self::Expr(expr) => expr.finish(ctx),
    }
  }
}
