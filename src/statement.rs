use quote::TokenStreamExt;
use quote::quote;
use nom::IResult;
use nom::combinator::value;

use crate::tokens::parenthesized;
use super::*;

/// A statement.
///
/// ```c
/// #define STMT int n = 1;
/// #define STMT do { \
///   call(); \
/// } while (0)
/// ```
#[derive(Debug)]
pub enum Statement {
  Expr(Expr),
  FunctionDecl(FunctionDecl),
  Decl(Decl),
  Block(Vec<Self>),
  If {
    condition: Expr,
    if_branch: Vec<Statement>,
    else_branch: Vec<Statement>
  },
  DoWhile { block: Vec<Statement>, condition: Expr },
}

impl Statement {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let condition = |input| parenthesized(Expr::parse)(input);
    let block = |input| map(Self::parse, |stmt| if let Self::Block(stmts) = stmt {
      stmts
    } else {
      vec![stmt]
    })(input);
    let semicolon_or_eof = |input| alt((
      value((), token(";")),
      value((), eof),
    ))(input);

    alt((
      map(
        delimited(terminated(token("{"), meta), separated_list0(meta, Self::parse), preceded(meta, token("}"))),
        Self::Block,
      ),
      map(
        tuple((
          preceded(terminated(token("if"), meta), condition),
          block,
          opt(preceded(
            delimited(meta, token("else"), meta),
            block,
          )),
        )),
        |(condition, if_branch, else_branch)| {
          Self::If { condition, if_branch, else_branch: else_branch.unwrap_or_default() }
        }
      ),
      map(
        preceded(
          terminated(token("do"), meta),
          pair(
            block,
            preceded(token("while"), condition),
          ),
        ),
        |(block, condition)| Self::DoWhile { block, condition }
      ),
      map(
        terminated(FunctionDecl::parse, semicolon_or_eof),
        Self::FunctionDecl,
      ),
      map(
        terminated(Decl::parse, alt((token(";"), map(eof, |_| "")))),
        Self::Decl,
      ),
      map(
        terminated(Expr::parse, alt((token(";"), map(eof, |_| "")))),
        Self::Expr,
      ),
    ))(tokens)
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    match self {
      Self::Expr(expr) => expr.visit(ctx),
      Self::FunctionDecl(f) => f.visit(ctx),
      Self::Decl(d) => d.visit(ctx),
      Self::Block(block) => {
        for stmt in block {
          stmt.visit(ctx);
        }
      },
      Self::If { condition, if_branch, else_branch } => {
        condition.visit(ctx);

        for stmt in if_branch {
          stmt.visit(ctx);
        }

        for stmt in else_branch {
          stmt.visit(ctx);
        }
      },
      Self::DoWhile { block, condition } => {
        for stmt in block {
          stmt.visit(ctx);
        }

        condition.visit(ctx);
      },
    }
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
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

  pub fn to_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}
