use quote::TokenStreamExt;
use nom::IResult;
use quote::quote;

use super::*;

/// A variable declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
  ty: Type,
  name: Identifier,
  rhs: Expr,
  is_static: bool,
}

impl Decl {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, ((static_storage, ty), name, _, rhs)) = tuple((
      permutation((opt(token("static")), Type::parse)),
      Identifier::parse, token("="), Expr::parse,
    ))(tokens)?;

    Ok((tokens, Self { ty, name, rhs, is_static: static_storage.is_some() }))
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    self.ty.finish(ctx)?;
    self.name.finish(ctx)?;
    self.rhs.finish(ctx)?;
    Ok(())
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    let ty = self.ty.to_token_stream(ctx);
    let name = self.name.to_token_stream(ctx);
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(if self.is_static {
      quote! { static mut #name: #ty = #rhs }
    } else {
      quote! { let mut #name: #ty = #rhs }
    })
  }

  pub fn to_token_stream(&self, ctx: &mut LocalContext) -> TokenStream {
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
    assert_eq!(id, Decl {
      ty: Type::Ptr {
        ty: Box::new(Type::BuiltIn(BuiltInType::Int)),
        mutable: true,
      },
      name: Identifier::Literal("abc".into()),
      rhs: Expr::Literal(Lit::Int(LitInt::new("123"))),
      is_static: false,
    });
  }
}
