#![warn(missing_debug_implementations)]

use std::collections::HashMap;
use std::str;
use nom::combinator::map;
use nom::branch::alt;
use nom::sequence::terminated;
use nom::combinator::eof;
use nom::sequence::pair;
use nom::sequence::tuple;
use nom::multi::separated_list0;
use nom::combinator::opt;
use nom::sequence::delimited;
use nom::branch::permutation;
use nom::sequence::preceded;
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use quote::TokenStreamExt;

mod error;
pub use error::*;

mod macro_sig;
pub use macro_sig::*;
mod macro_body;
pub use macro_body::*;

mod context;
pub use context::*;

mod tokens;
use tokens::*;

mod asm;
pub use asm::*;

mod ty;
pub use ty::*;

mod identifier;
pub use identifier::*;

mod expr;
pub use expr::*;

mod function_call;
pub use function_call::*;

mod function_decl;
pub use function_decl::*;

mod literal;
pub use literal::*;

mod statement;
pub use statement::*;

mod decl;
pub use decl::*;

mod stringify;
pub use stringify::*;

/// A variable-like macro.
#[derive(Debug)]
pub struct VarMacro<'t> {
  pub name: &'t str,
  pub body: MacroBody,
}

impl<'t> VarMacro<'t> {
  pub fn parse<'i>(name: &'t str, body: &'i [&'t str]) -> Result<Self, nom::Err<nom::error::Error<&'i [&'t str]>>> {
    let (_, body) = MacroBody::parse(body)?;
    Ok(Self { name, body })
  }

  pub fn write(
    &mut self,
    _variable_type: impl FnMut(&str, &str) -> Option<syn::Type>,
    _return_type: impl FnMut(&str) -> Option<syn::Type>,
  ) -> Result<TokenStream, ()> {
    let mut tokens = TokenStream::new();

    let mut ctx = Context {
      args: HashMap::new(),
      export_as_macro: false,
      functions: HashMap::new(),
      variables: HashMap::new(),
      macro_variables: HashMap::new(),
    };
    self.body.visit(&mut ctx);

    match &self.body {
      MacroBody::Block(_) => return Err(()),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut tokens),
    }

    Ok(tokens)
  }
}

/// A function-like macro.
#[derive(Debug)]
pub struct FnMacro<'t> {
  pub name: &'t str,
  pub args: Vec<(&'t str, MacroArgType)>,
  pub body: MacroBody,
}

impl<'t> FnMacro<'t> {
  pub fn parse<'i>(sig: &'t str, body: &'i [&'t str]) -> Result<Self, nom::Err<nom::error::Error<&'i [&'t str]>>> {
    let (_, sig) = MacroSig::parse(&tokenize_name(sig.as_bytes())).unwrap();
    let (_, body) = MacroBody::parse(body)?;

    let args = sig.args.into_iter().map(|arg| (arg, MacroArgType::Unknown)).collect();
    Ok(Self { name: sig.name, args, body })
  }

  pub fn write(
    &mut self,
    mut variable_type: impl FnMut(&str, &str) -> Option<syn::Type>,
    mut return_type: impl FnMut(&str) -> Option<syn::Type>,
  ) -> Result<TokenStream, ()> {
    let mut tokens = TokenStream::new();

    let mut args = HashMap::new();
    for (arg, ty) in self.args.clone() {
      args.insert(arg, ty);
    }

    let mut ctx = Context {
      args,
      export_as_macro: false,
      functions: HashMap::new(),
      variables: HashMap::new(),
      macro_variables: HashMap::new(),
    };
    self.body.visit(&mut ctx);

    let mut export_as_macro = !ctx.args.iter().all(|(_, ty)| *ty == MacroArgType::Unknown);
    let func_args = self.args.iter().filter_map(|(arg, _)| {
      let id = Ident::new(arg, Span::call_site());
      variable_type(self.name, arg).map(|ty| quote! { #id: #ty })
    }).collect::<Vec<_>>();

    if func_args.len() != self.args.len() {
      export_as_macro = true;
    }

    let name = Ident::new(self.name, Span::call_site());

    let mut body = TokenStream::new();
    match &self.body {
      MacroBody::Block(stmt) => stmt.to_tokens(&mut ctx, &mut body),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut body),
    }

    if export_as_macro {
      let args = self.args.iter().map(|(arg, ty)| {
        let id = Ident::new(arg, Span::call_site());

        if *ty == MacroArgType::Ident {
          quote! { $#id:ident }
        } else {
          quote! { $#id:expr }
        }
      }).collect::<Vec<_>>();

      tokens.append_all(quote! {
        macro_rules! #name {
          (#(#args),*) => {
            #body
          };
        }
      })
    } else {
      let return_type = return_type(self.name).map(|ty| {
        quote! { -> #ty }
      });

      let semicolon = if return_type.is_none() {
        Some(quote! { ; })
      } else {
        None
      };

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
