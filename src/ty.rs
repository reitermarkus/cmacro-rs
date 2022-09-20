use quote::TokenStreamExt;

use super::*;

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  Identifier { name: Identifier, is_struct: bool },
  Ptr { ty: Box<Self>, mutable: bool },
}

impl Type {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, (_, (strvct, ty), _)) = tuple((
      many0_count(token("const")), pair(opt(token("struct")), Identifier::parse), many0_count(token("const")),
    ))(tokens)?;

    fold_many0(
      preceded(pair(token("*"), meta), many0_count(token("const"))),
      move || Type::Identifier { name: ty.clone(), is_struct: strvct.is_some() },
      |acc, constness| {
        Type::Ptr { ty: Box::new(acc), mutable: constness == 0 }
      },
    )(tokens)
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    match self {
      Self::Identifier { name, .. } => name.visit(ctx),
      Self::Ptr { ty, .. } => ty.visit(ctx),
    }
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
    match self {
      Self::Identifier { name, .. } => {
        if matches!(name, Identifier::Literal(id) if id == "void") {
          tokens.append_all(quote! {
            ::core::ffi::c_void
          })
        } else {
          name.to_tokens(ctx, tokens)
        }
      },
      Self::Ptr { ty, mutable } => {
        let ty = ty.to_token_stream(ctx);

        tokens.append_all(if *mutable {
          quote! { *mut #ty }
        } else {
          quote! { *const #ty }
        })
      }
    }
  }

  pub fn to_token_stream(&self, ctx: &mut Context) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}
