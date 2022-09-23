use proc_macro2::TokenStream;
use nom::sequence::pair;
use quote::TokenStreamExt;
use nom::IResult;
use quote::quote;
use nom::branch::permutation;
use nom::combinator::opt;
use nom::multi::separated_list0;
use nom::sequence::tuple;

use crate::LocalContext;
use super::tokens::parenthesized;
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
      parenthesized(
        separated_list0(pair(meta, token(",")), pair(Type::parse, Identifier::parse)),
      ),
    ))(tokens)?;

    Ok((tokens, Self { ret_ty, name, args }))
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    self.ret_ty.finish(ctx)?;
    self.name.finish(ctx)?;
    for (ty, arg) in self.args.iter_mut() {
      ty.finish(ctx)?;
      arg.finish(ctx)?;
    }

    Ok(())
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
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