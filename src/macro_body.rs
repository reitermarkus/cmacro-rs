use std::fmt::Debug;

use nom::{
  branch::alt,
  combinator::{all_consuming, map},
  IResult,
};

use crate::{
  ast::{meta, Type},
  CodegenContext, Expr, LocalContext, MacroToken, Statement,
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
  pub(crate) fn parse<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, _) = meta(tokens)?;

    if tokens.is_empty() {
      return Ok((tokens, Self::Statement(Statement::Block(vec![]))))
    }

    let (tokens, body) = alt((
      all_consuming(map(|tokens| Expr::parse(tokens), Self::Expr)),
      all_consuming(map(|tokens| Statement::parse(tokens), Self::Statement)),
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
