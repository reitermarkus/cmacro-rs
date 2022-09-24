use nom::branch::permutation;
use nom::combinator::opt;
use nom::sequence::tuple;
use nom::IResult;
use proc_macro2::TokenStream;
use quote::quote;
use quote::TokenStreamExt;

use super::*;
use crate::{CodegenContext, LocalContext};

/// A variable declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
  ty: Type,
  name: Identifier,
  rhs: Expr,
  is_static: bool,
}

impl Decl {
  pub fn parse<'i, 't>(tokens: &'i [&'t [u8]]) -> IResult<&'i [&'t [u8]], Self> {
    let (tokens, ((static_storage, ty), name, _, rhs)) =
      tuple((permutation((opt(token("static")), Type::parse)), Identifier::parse, token("="), Expr::parse))(tokens)?;

    Ok((tokens, Self { ty, name, rhs, is_static: static_storage.is_some() }))
  }

  pub(crate) fn finish<'t, 'g, C>(&mut self, ctx: &mut LocalContext<'t, 'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    self.ty.finish(ctx)?;
    self.name.finish(ctx)?;
    self.rhs.finish(ctx)?;

    // A declaration has no type.
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    let ty = self.ty.to_token_stream(ctx);
    let name = self.name.to_token_stream(ctx);
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(if self.is_static {
      quote! { static mut #name: #ty = #rhs }
    } else {
      quote! { let mut #name: #ty = #rhs }
    })
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse() {
    let (_, id) = Decl::parse(&["int", "*", "abc", "=", "123"]).unwrap();
    assert_eq!(
      id,
      Decl {
        ty: Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Int)), mutable: true },
        name: Identifier::Literal("abc".into()),
        rhs: Expr::Literal(Lit::Int(LitInt { value: 123, suffix: None })),
        is_static: false,
      }
    );
  }
}
