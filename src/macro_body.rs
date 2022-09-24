use std::ops::RangeFrom;
use std::ops::RangeTo;

use nom::branch::alt;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::AsChar;
use nom::Compare;
use nom::FindSubstring;
use nom::FindToken;
use nom::IResult;
use nom::InputIter;
use nom::InputLength;
use nom::InputTake;
use nom::InputTakeAtPosition;
use nom::Offset;
use nom::ParseTo;
use nom::Slice;

use crate::{
  ast::{meta, Type},
  CodegenContext, Expr, LocalContext, Statement,
};

/// The body of a macro.
#[derive(Debug)]
pub enum MacroBody {
  Block(Statement),
  Expr(Expr),
}

impl MacroBody {
  pub fn parse<'i, I, C>(input: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputTake
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
