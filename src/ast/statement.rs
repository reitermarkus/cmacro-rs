use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
};

use nom::{
  branch::alt,
  combinator::{eof, map, opt, value},
  multi::separated_list0,
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
#[derive(Debug, Clone)]
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
        delimited(terminated(token("{"), meta), separated_list0(meta, Self::parse), preceded(meta, token("}"))),
        Self::Block,
      ),
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
      map(terminated(FunctionDecl::parse, semicolon_or_eof), Self::FunctionDecl),
      map(terminated(Decl::parse, alt((token(";"), map(eof, |_| "")))), Self::Decl),
      map(terminated(Expr::parse, alt((token(";"), map(eof, |_| "")))), Self::Expr),
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

        tokens.append_all(quote! {
          if #condition {
            #(#if_branch)*
          } else {
            #(#else_branch)*
          }
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
