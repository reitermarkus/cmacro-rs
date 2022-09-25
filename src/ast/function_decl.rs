use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
};

use nom::{
  branch::permutation,
  combinator::opt,
  multi::separated_list0,
  sequence::{pair, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{tokens::parenthesized, *};
use crate::{CodegenContext, LocalContext};

/// A function declaration.
///
/// ```c
/// #define function_decl void f(int a, int b, int c)
/// ```
#[derive(Debug)]
pub struct FunctionDecl {
  ret_ty: Type,
  name: Identifier,
  args: Vec<(Type, Identifier)>,
}

impl FunctionDecl {
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
    let (tokens, ((_, ret_ty), name, args)) = tuple((
      permutation((opt(token("static")), Type::parse)),
      Identifier::parse,
      parenthesized(separated_list0(pair(meta, token(",")), pair(Type::parse, Identifier::parse))),
    ))(tokens)?;

    Ok((tokens, Self { ret_ty, name, args }))
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    self.ret_ty.finish(ctx)?;
    self.name.finish(ctx)?;
    for (ty, arg) in self.args.iter_mut() {
      ty.finish(ctx)?;
      arg.finish(ctx)?;
    }

    // A declaration has no type.
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let name = self.name.to_token_stream(ctx);
    let args = self
      .args
      .iter()
      .map(|(ty, arg)| {
        let ty = ty.to_token_stream(ctx);
        let arg = arg.to_token_stream(ctx);
        quote! { #arg: #ty }
      })
      .collect::<Vec<_>>();
    let ret_ty = self.ret_ty.to_token_stream(ctx);

    tokens.append_all(quote! {
      extern "C" {
        pub fn #name(#(#args),*) -> #ret_ty;
      }
    })
  }
}
