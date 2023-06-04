use std::fmt::Debug;

use nom::{branch::permutation, combinator::opt, sequence::tuple, IResult};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::*;
use crate::{CodegenContext, LocalContext, MacroToken};

/// A variable declaration.
///
/// ```c
/// #define DECL int var = 77
/// ```
#[derive(Debug, Clone, PartialEq)]
#[allow(missing_docs)]
pub struct VarDecl<'t> {
  pub ty: Type<'t>,
  pub name: Expr<'t>,
  pub rhs: Expr<'t>,
  pub is_static: bool,
}

impl<'t> VarDecl<'t> {
  /// Parse a variable declaration.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, ((static_storage, ty), name, _, rhs)) =
      tuple((permutation((opt(id("static")), Type::parse)), Expr::parse_concat_ident, punct("="), Expr::parse))(
        tokens,
      )?;

    Ok((tokens, Self { ty, name, rhs, is_static: static_storage.is_some() }))
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.ty.finish(ctx)?;
    self.name.finish(ctx)?;
    self.rhs.finish(ctx)?;

    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let ty = self.ty.to_token_stream(ctx);
    let name = self.name.to_token_stream(ctx);
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(if self.is_static {
      quote! { static mut #name: #ty = #rhs }
    } else {
      quote! { let mut #name: #ty = #rhs }
    })
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_token::{id as macro_id, int as macro_int, punct as macro_punct, tokens};

  #[test]
  fn parse() {
    let (_, id) =
      VarDecl::parse(tokens![macro_id!(int), macro_punct!("*"), macro_id!(abc), macro_punct!("="), macro_int!(123)])
        .unwrap();
    assert_eq!(
      id,
      VarDecl {
        ty: Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Int)), mutable: true },
        name: var!(abc),
        rhs: Expr::Literal(Lit::Int(LitInt { value: 123, suffix: None })),
        is_static: false,
      }
    );
  }
}
