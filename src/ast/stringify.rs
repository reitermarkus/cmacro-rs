use std::fmt::Debug;

use nom::{
  branch::alt,
  combinator::map,
  sequence::{preceded, terminated},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  tokens::{macro_arg, macro_id, meta, punct},
  BuiltInType, Expr, IdentifierExpr, Type, TypeQualifier, Var,
};
use crate::{codegen::quote_c_char_ptr, CodegenContext, LocalContext, MacroArgType, MacroToken};

/// Stringification of a macro argument.
///
/// ```c
/// #define STRINGIFY(x) #x
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stringify<'t> {
  pub(crate) arg: Box<Expr<'t>>,
}

impl<'t> Stringify<'t> {
  /// Parse a stringification expression.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    preceded(
      terminated(punct("#"), meta),
      alt((
        map(macro_arg, |arg| Self { arg: Box::new(Expr::Var(Var { name: IdentifierExpr::Arg(arg) })) }),
        map(macro_id, |id| Self { arg: Box::new(Expr::Var(Var { name: IdentifierExpr::Plain(id) })) }),
      )),
    )(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match &mut *self.arg {
      Expr::Var(Var { name: IdentifierExpr::Arg(arg) }) => {
        let arg_ty = ctx.arg_type_mut(arg.index());
        if *arg_ty != MacroArgType::Ident {
          *arg_ty = MacroArgType::Expr;
        }
      },
      Expr::Var(Var { name: IdentifierExpr::Plain(name) }) if matches!(name.as_str(), "__LINE__" | "__FILE__") => {
        ctx.export_as_macro = true;
      },
      _ => return Err(crate::CodegenError::UnsupportedExpression("stringification".to_owned())),
    }

    Ok(Some(Type::Qualified {
      ty: Box::new(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)) }),
      qualifier: TypeQualifier::Const,
    }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream_inner<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>) -> TokenStream {
    let expr = match &*self.arg {
      Expr::Var(Var { name: IdentifierExpr::Arg(arg) }) => {
        let id = Ident::new(ctx.arg_name(arg.index()), Span::call_site());
        Some(quote! { $#id })
      },
      Expr::Var(Var { name: IdentifierExpr::Plain(name) }) => match name.as_str() {
        "__LINE__" => {
          let trait_prefix = ctx.trait_prefix().into_iter();
          Some(quote! { #(#trait_prefix::)*line!() })
        },
        "__FILE__" => {
          let trait_prefix = ctx.trait_prefix().into_iter();
          let file = quote! { #(#trait_prefix::)*file!() };
          let trait_prefix = ctx.trait_prefix().into_iter();
          return quote! { #(#trait_prefix::)*format!("{:?}", #file) }
        },
        _ => None,
      },
      _ => None,
    }
    .into_iter();

    let trait_prefix = ctx.trait_prefix().into_iter();
    quote! { #(#trait_prefix::)*stringify!(#(#expr),*) }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>) -> TokenStream {
    let trait_prefix = ctx.trait_prefix().into_iter();

    let stringify = self.to_token_stream_inner(ctx);

    quote_c_char_ptr(ctx, quote! { #(#trait_prefix::)*concat!(#stringify, '\0') })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::ast::{arg, parse_tokens, punct};

  #[test]
  fn parse_stringify() {
    parse_tokens!(
      Stringify => [punct!("#"), arg!(0)],
      Stringify { arg: Box::new(Expr::Var(Var { name: IdentifierExpr::Arg(arg!(0)) })) },
    );
  }
}
