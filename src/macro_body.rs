use nom::IResult;
use nom::combinator::map;
use nom::combinator::all_consuming;
use nom::branch::alt;

use crate::{LocalContext, Statement, Expr, ast::meta};

/// The body of a macro.
#[derive(Debug)]
pub enum MacroBody {
  Block(Statement),
  Expr(Expr),
}

impl MacroBody {
  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
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

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    match self {
      Self::Block(stmt) => stmt.finish(ctx)?,
      Self::Expr(expr) => expr.finish(ctx)?,
    }

    Ok(())
  }
}
