#![warn(missing_debug_implementations)]

use std::ops::RangeFrom;
use std::ops::RangeTo;
use std::collections::HashMap;
use std::str;

use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use quote::TokenStreamExt;
use nom::AsChar;
use nom::Compare;
use nom::FindSubstring;
use nom::FindToken;
use nom::IResult;
use nom::InputIter;
use nom::InputLength;
use nom::InputTake;
use nom::InputTakeAtPosition;
use nom::Offset;
use nom::ParseTo;
use nom::Slice;

pub mod ast;
pub use ast::*;
mod error;
pub use error::*;
mod macro_sig;
pub use macro_sig::*;
mod macro_body;
pub use macro_body::*;
mod context;
pub use context::*;

/// A variable-like macro.
#[derive(Debug, Clone)]
pub struct VarMacro {
  pub name: String,
  pub expr: Expr,
}

impl VarMacro {
  pub fn parse<'i, I, C>(name: &str, body: &'i [I]) -> Result<Self, crate::Error>
  where
    I: InputTake
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
    let body = match MacroBody::parse(body) {
      Ok((_, body)) => body,
      Err(_) => return Err(crate::Error::ParserError),
    };

    let expr = match body {
      MacroBody::Block(_) => return Err(crate::Error::InvalidVarMacro),
      MacroBody::Expr(expr) => expr,
    };

    Ok(Self { name: name.to_owned(), expr })
  }

  pub fn generate<C>(&mut self, cx: &C) -> Result<(TokenStream, Option<Type>), crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let mut ctx = LocalContext { args: HashMap::new(), export_as_macro: false, global_context: cx };

    let ty = self.expr.finish(&mut ctx)?;
    self.expr.to_tokens(&mut ctx, &mut tokens);

    Ok((tokens, ty))
  }

  pub fn name(&self) -> &str {
    self.name.as_str()
  }
}

/// A function-like macro.
#[derive(Debug)]
pub struct FnMacro {
  pub name: String,
  pub args: Vec<(String, MacroArgType)>,
  pub body: MacroBody,
}

impl FnMacro {
  pub fn parse<'i, I, C>(
    sig: &'i [I],
    body: &'i [I],
  ) -> Result<Self, nom::Err<nom::error::Error<&'i [I]>>>

  where
    I: InputTake
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
    // let sig: Vec<&'s [u8]> = tokenize_name(sig);
    let (_, sig) = MacroSig::parse(sig)?;
    let (_, body) = MacroBody::parse(body)?;

    let args = sig.args.into_iter().map(|arg| (arg, MacroArgType::Unknown)).collect();
    Ok(Self { name: sig.name, args, body })
  }

  pub fn generate<C>(
    &mut self,
    mut variable_type: impl FnMut(&str, &str) -> Option<syn::Type>,
    mut return_type: impl FnMut(&str) -> Option<syn::Type>,
    cx: &C,
  ) -> Result<TokenStream, crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let mut args = HashMap::new();
    for (arg, ty) in self.args.clone() {
      args.insert(arg, ty);
    }

    let mut ctx = LocalContext { args, export_as_macro: false, global_context: cx };
    self.body.finish(&mut ctx)?;

    let mut export_as_macro = ctx.is_variadic() || !ctx.args.iter().all(|(_, ty)| *ty == MacroArgType::Unknown);
    let func_args = self
      .args
      .iter()
      .filter_map(|(arg, _)| {
        let id = Ident::new(arg, Span::call_site());
        variable_type(&self.name, arg).map(|ty| quote! { #id: #ty })
      })
      .collect::<Vec<_>>();

    if func_args.len() != self.args.len() {
      export_as_macro = true;
    }

    let name = Ident::new(&self.name, Span::call_site());

    let mut body = TokenStream::new();
    match &self.body {
      MacroBody::Block(stmt) => stmt.to_tokens(&mut ctx, &mut body),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut body),
    }

    if export_as_macro {
      let args = self
        .args
        .iter()
        .map(|(arg, ty)| {
          let id = Ident::new(arg, Span::call_site());

          if *ty == MacroArgType::Ident {
            quote! { $#id:ident }
          } else {
            quote! { $#id:expr }
          }
        })
        .collect::<Vec<_>>();

      tokens.append_all(quote! {
        macro_rules! #name {
          (#(#args),*) => {
            #body
          };
        }
      })
    } else {
      let return_type = return_type(&self.name).map(|ty| {
        quote! { -> #ty }
      });

      let semicolon = if return_type.is_none() { Some(quote! { ; }) } else { None };

      tokens.append_all(quote! {
        #[allow(non_snake_case)]
        #[inline(always)]
        pub unsafe extern "C" fn #name(#(mut #func_args),*) #return_type {
          #body
          #semicolon
        }
      })
    }

    Ok(tokens)
  }
}
