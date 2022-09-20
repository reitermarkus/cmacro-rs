use quote::TokenStreamExt;

use super::*;

/// A function declaration.
#[derive(Debug)]
pub struct FunctionDecl {
  ret_ty: Type,
  name: Identifier,
  args: Vec<(Type, Identifier)>,
}

impl FunctionDecl {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, ((_, ret_ty), name, args)) = tuple((
      permutation((opt(token("static")), Type::parse)),
      Identifier::parse,
      delimited(
        pair(token("("), meta),
        separated_list0(pair(meta, token(",")), pair(Type::parse, Identifier::parse)),
        pair(meta, token(")")),
      ),
    ))(tokens)?;

    Ok((tokens, Self { ret_ty, name, args }))
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    self.ret_ty.visit(ctx);
    self.name.visit(ctx);
    for (ty, arg) in self.args.iter_mut() {
      ty.visit(ctx);
      arg.visit(ctx);
    }
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
    let name = self.name.to_token_stream(ctx);
    let args = self.args.iter().map(|(ty, arg)| {
      let ty = ty.to_token_stream(ctx);
      let arg = arg.to_token_stream(ctx);
      quote! { #arg: #ty }
    }).collect::<Vec<_>>();
    let ret_ty = self.ret_ty.to_token_stream(ctx);

    tokens.append_all(quote! {
      extern "C" {
        pub fn #name(#(#args),*) -> #ret_ty;
      }
    })
  }
}
