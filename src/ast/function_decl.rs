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

use super::{tokens::parenthesized, *};
use crate::{CodegenContext, LocalContext, MacroArgType, ParseContext};

/// A function declaration.
///
/// ```c
/// #define FUNC_DECL void f(int a, int b, int c)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDecl {
  ret_ty: Type,
  name: Expr,
  args: Vec<(Type, Expr)>,
}

impl FunctionDecl {
  /// Parse a function declaration.
  pub(crate) fn parse<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, ((_, ret_ty), name, args)) = tuple((
      permutation((opt(token("static")), |tokens| Type::parse(tokens, ctx))),
      |tokens| Expr::parse_concat_ident(tokens, ctx),
      parenthesized(separated_list0(
        pair(meta, token(",")),
        pair(|tokens| Type::parse(tokens, ctx), |tokens| Expr::parse_concat_ident(tokens, ctx)),
      )),
    ))(tokens)?;

    Ok((tokens, Self { ret_ty, name, args }))
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.ret_ty.finish(ctx)?;
    self.name.finish(ctx)?;

    if let Expr::Arg { name: Identifier::Literal(id) } = &self.name {
      if let Some(arg_type) = ctx.arg_type_mut(id.as_str()) {
        *arg_type = MacroArgType::Ident;
      }
    }

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
