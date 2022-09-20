use quote::TokenStreamExt;

use super::*;

/// A variable declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl<'t> {
  ty: Type,
  name: Identifier,
  rhs: Expr<'t>,
  is_static: bool,
}

impl<'t> Decl<'t> {
  pub fn parse<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, ((static_storage, ty), name, _, rhs)) = tuple((
      permutation((opt(token("static")), Type::parse)),
      Identifier::parse, token("="), Expr::parse,
    ))(tokens)?;

    Ok((tokens, Self { ty, name, rhs, is_static: static_storage.is_some() }))
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    self.ty.visit(ctx);
    self.name.visit(ctx);
    self.rhs.visit(ctx);
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
    let ty = self.ty.to_token_stream(ctx);
    let name = self.name.to_token_stream(ctx);
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(if self.is_static {
      quote! { static mut #name: #ty = #rhs }
    } else {
      quote! { let mut #name: #ty = #rhs }
    })
  }

  pub fn to_token_stream(&self, ctx: &mut Context) -> TokenStream {
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
        ty: Box::new(Type::Identifier { name: Identifier::Literal("int".into()), is_struct: false }),
        mutable: true,
      },
      name: Identifier::Literal("abc".into()),
      rhs: Expr::Literal(Lit::Int(LitInt::new("123"))),
      is_static: false,
    });
  }
}
