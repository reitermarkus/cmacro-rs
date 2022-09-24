#![warn(missing_debug_implementations)]

use std::{
  collections::HashMap,
  ops::{RangeFrom, RangeTo},
  str,
};

use nom::{
  branch::alt,
  combinator::{all_consuming, map, opt},
  multi::separated_list0,
  sequence::tuple,
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

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
  pub fn parse<I, C>(name: I, body: &[I]) -> Result<Self, crate::Error>
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
    let name = if let Ok((_, name)) = identifier(&[name]) { name } else { return Err(crate::Error::ParserError) };

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
  fn parse_args<'i, I>(input: &'i [I]) -> IResult<&'i [I], Vec<String>>
  where
    I: InputTake + InputLength + InputIter + Compare<&'static str> + FindSubstring<&'static str> + Clone,
    <I as InputIter>::Item: AsChar,
  {
    all_consuming(parenthesized(alt((
      map(token("..."), |var_arg| vec![var_arg.to_owned()]),
      map(
        tuple((
          separated_list0(tuple((meta, token(","), meta)), identifier),
          opt(tuple((tuple((meta, token(","), meta)), map(token("..."), |var_arg| var_arg.to_owned())))),
        )),
        |(arguments, var_arg)| {
          let mut arguments = arguments.to_vec();

          if let Some((_, var_arg)) = var_arg {
            arguments.push(var_arg);
          }

          arguments
        },
      ),
    ))))(input)
  }

  pub fn parse<I, C>(name: I, args: &[I], body: &[I]) -> Result<Self, crate::Error>
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
    let (_, name) = identifier(&[name]).map_err(|_| crate::Error::ParserError)?;

    let (_, args) = Self::parse_args(args).map_err(|_| crate::Error::ParserError)?;
    let (_, body) = MacroBody::parse(body).map_err(|_| crate::Error::ParserError)?;

    let args = args.into_iter().map(|arg| (arg, MacroArgType::Unknown)).collect();
    Ok(Self { name: name, args, body })
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
