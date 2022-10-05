use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
};

use nom::{
  branch::alt,
  combinator::{eof, map, opt, value},
  multi::many0,
  sequence::{delimited, pair, preceded, terminated, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{tokens::parenthesized, *};
use crate::{CodegenContext, LocalContext};

/// A statement.
///
/// ```c
/// #define STMT int n = 1;
/// #define STMT do { \
///   call(); \
/// } while (0)
/// ```
#[derive(Debug, Clone, PartialEq)]
#[allow(missing_docs)]
pub enum Statement {
  /// An expression.
  Expr(Expr),
  /// A function declaration.
  FunctionDecl(FunctionDecl),
  /// A variable declaration.
  Decl(Decl),
  /// A block containing multiple statements.
  Block(Vec<Self>),
  /// An if-condition.
  If { condition: Expr, if_branch: Vec<Statement>, else_branch: Vec<Statement> },
  /// A do-while condition.
  DoWhile { block: Vec<Statement>, condition: Expr },
}

impl Statement {
  /// Parse a statement.
  pub fn parse<I, C>(tokens: &[I]) -> IResult<&[I], Self>
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
    let condition = |input| parenthesized(Expr::parse)(input);
    let block = |input| map(Self::parse, |stmt| if let Self::Block(stmts) = stmt { stmts } else { vec![stmt] })(input);
    let semicolon_or_eof = |input| alt((value((), token(";")), value((), eof)))(input);

    alt((
      map(
        tuple((
          preceded(terminated(token("if"), meta), condition),
          block,
          opt(preceded(delimited(meta, token("else"), meta), block)),
        )),
        |(condition, if_branch, else_branch)| Self::If {
          condition,
          if_branch,
          else_branch: else_branch.unwrap_or_default(),
        },
      ),
      map(
        preceded(terminated(token("do"), meta), pair(block, preceded(token("while"), condition))),
        |(block, condition)| Self::DoWhile { block, condition },
      ),
      map(
        delimited(terminated(token("{"), meta), many0(preceded(meta, Self::parse)), preceded(meta, token("}"))),
        Self::Block,
      ),
      map(terminated(FunctionDecl::parse, semicolon_or_eof), Self::FunctionDecl),
      map(terminated(Decl::parse, semicolon_or_eof), Self::Decl),
      map(terminated(Expr::parse, semicolon_or_eof), Self::Expr),
    ))(tokens)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    match self {
      Self::Expr(expr) => {
        expr.finish(ctx)?;
      },
      Self::FunctionDecl(f) => {
        f.finish(ctx)?;
      },
      Self::Decl(d) => {
        d.finish(ctx)?;
      },
      Self::Block(block) => {
        for stmt in block {
          stmt.finish(ctx)?;
        }
      },
      Self::If { condition, if_branch, else_branch } => {
        condition.finish(ctx)?;

        for stmt in if_branch {
          stmt.finish(ctx)?;
        }

        for stmt in else_branch {
          stmt.finish(ctx)?;
        }
      },
      Self::DoWhile { block, condition } => {
        for stmt in block {
          stmt.finish(ctx)?;
        }

        condition.finish(ctx)?;
      },
    }

    Ok(Some(Type::BuiltIn(BuiltInType::Void)))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Expr(expr) => {
        let expr = expr.to_token_stream(ctx);
        tokens.append_all(quote! { #expr; })
      },
      Self::FunctionDecl(f) => f.to_tokens(ctx, tokens),
      Self::Decl(d) => {
        let decl = d.to_token_stream(ctx);
        tokens.append_all(quote! { #decl; })
      },
      Self::Block(block) => {
        let block = block.iter().map(|stmt| stmt.to_token_stream(ctx)).collect::<Vec<_>>();

        tokens.append_all(quote! {
          {
            #(#block)*
          }
        })
      },
      Self::If { condition, if_branch, else_branch } => {
        let condition = condition.to_token_stream(ctx);
        let if_branch = if_branch.iter().map(|stmt| stmt.to_token_stream(ctx)).collect::<Vec<_>>();
        let else_branch = else_branch.iter().map(|stmt| stmt.to_token_stream(ctx)).collect::<Vec<_>>();
        let else_branch = if else_branch.is_empty() { None } else { Some(quote! { else { #(#else_branch);* } }) };

        tokens.append_all(quote! {
          if #condition {
            #(#if_branch)*
          } #else_branch
        })
      },
      Self::DoWhile { block, condition } => {
        let block = block.iter().map(|stmt| stmt.to_token_stream(ctx)).collect::<Vec<_>>();
        let condition = condition.to_token_stream(ctx);

        tokens.append_all(quote! {
          loop {
            #(#block)*

            if #condition == Default::default() {
              break
            }
          }
        })
      },
    }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_expr() {
    let (_, stmt) = Statement::parse(&["a", "+=", "2", ";"]).unwrap();
    assert_eq!(
      stmt,
      Statement::Expr(Expr::Binary(Box::new(BinaryExpr { lhs: var!(a), op: BinaryOp::AddAssign, rhs: lit!(2) })))
    );
  }

  #[test]
  fn parse_empty_block() {
    let (_, stmt) = Statement::parse(&["{", "}"]).unwrap();
    assert_eq!(stmt, Statement::Block(vec![]));
  }

  #[test]
  fn parse_block() {
    let (_, stmt) = Statement::parse(&["{", "int", "a", "=", "0", ";", "}"]).unwrap();
    assert_eq!(
      stmt,
      Statement::Block(vec![Statement::Decl(Decl {
        ty: ty!(BuiltInType::Int),
        name: id!(a),
        rhs: lit!(0),
        is_static: false
      })])
    );
  }

  #[test]
  fn parse_if_stmt() {
    let (_, stmt) = Statement::parse(&["if", "(", "a", ")", "b", ";"]).unwrap();
    assert_eq!(
      stmt,
      Statement::If { condition: var!(a), if_branch: vec![Statement::Expr(var!(b))], else_branch: vec![] }
    );
  }

  #[test]
  fn parse_if_else_stmt() {
    let (_, stmt) = Statement::parse(&["if", "(", "a", ")", "b", ";", "else", "c", ";"]).unwrap();
    assert_eq!(
      stmt,
      Statement::If {
        condition: var!(a),
        if_branch: vec![Statement::Expr(var!(b))],
        else_branch: vec![Statement::Expr(var!(c))],
      }
    );
  }

  #[test]
  fn parse_if_block() {
    let (_, stmt) = Statement::parse(&["if", "(", "a", ")", "{", "b", ";", "}"]).unwrap();
    assert_eq!(
      stmt,
      Statement::If { condition: var!(a), if_branch: vec![Statement::Expr(var!(b))], else_branch: vec![] }
    );
  }

  #[test]
  fn parse_if_else_block() {
    let (_, stmt) = Statement::parse(&["if", "(", "a", ")", "{", "b", ";", "}", "else", "{", "c", ";", "}"]).unwrap();
    assert_eq!(
      stmt,
      Statement::If {
        condition: var!(a),
        if_branch: vec![Statement::Expr(var!(b))],
        else_branch: vec![Statement::Expr(var!(c))]
      }
    );
  }

  #[test]
  fn parse_do_while_stmt() {
    let (_, stmt) = Statement::parse(&["do", "a", ";", "while", "(", "b", ")"]).unwrap();
    assert_eq!(stmt, Statement::DoWhile { block: vec![Statement::Expr(var!(a))], condition: var!(b) });
  }

  #[test]
  fn parse_do_while_block() {
    let (_, stmt) = Statement::parse(&["do", "{", "a", ";", "}", "while", "(", "b", ")"]).unwrap();
    assert_eq!(stmt, Statement::DoWhile { block: vec![Statement::Expr(var!(a))], condition: var!(b) });
  }
}
