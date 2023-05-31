use std::fmt::Debug;

use nom::{
  branch::permutation,
  combinator::opt,
  multi::separated_list0,
  sequence::{pair, tuple},
  IResult,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{
  tokens::{parenthesized, punct},
  *,
};
use crate::{CodegenContext, LocalContext, MacroArgType, MacroToken};

/// A function declaration.
///
/// ```c
/// #define FUNC_DECL void f(int a, int b, int c)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDecl<'t> {
  ret_ty: Type<'t>,
  name: Expr<'t>,
  args: Vec<(Type<'t>, Expr<'t>)>,
}

impl<'t> FunctionDecl<'t> {
  /// Parse a function declaration.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, ((_, ret_ty), name, args)) = tuple((
      permutation((opt(id("static")), Type::parse)),
      Expr::parse_concat_ident,
      parenthesized(separated_list0(pair(meta, punct(",")), pair(Type::parse, Expr::parse_concat_ident))),
    ))(tokens)?;

    Ok((tokens, Self { ret_ty, name, args }))
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.ret_ty.finish(ctx)?;
    self.name.finish(ctx)?;

    if let Expr::Arg(arg) = &self.name {
      *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
    }

    for (ty, arg) in self.args.iter_mut() {
      ty.finish(ctx)?;
      arg.finish(ctx)?;
    }

    // A declaration has no type.
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
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
