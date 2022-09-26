//! A library for parsing C macros.
//!
//! This crate allows parsing C macros, evaluating them and generating Rust code from them.
//!
//! Both variable-like macros (e.g. `#define VAR 4 + 7 * 82`) as well as function-like macros
//! (e.g. `#define FUNC(a, b, c) a + b * c`) are supported.
//!
//! See the [`VarMacro`] and [`FnMacro`] functions on how to parse macros.

#![warn(missing_debug_implementations)]
#![warn(missing_docs)]

use std::{
  collections::HashMap,
  fmt::Debug,
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
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), cmacro::Error> {
/// use cmacro::VarMacro;
///
/// // #define VAR 4 + 7 + 82
/// let name = "VAR";
/// let value = ["4", "+", "7", "*", "82"];
///
/// let mut var_macro = VarMacro::parse(name, &value)?;
/// let (output, ty) = var_macro.generate(())?;
/// assert_eq!(output.to_string(), "578");
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct VarMacro {
  /// The name of this variable macro.
  pub name: String,
  /// The value of this variable macro.
  pub value: Expr,
}

impl VarMacro {
  /// Parse a variable-like macro from a name and value tokens.
  pub fn parse<I, C>(name: I, value: &[I]) -> Result<Self, crate::Error>
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
    let name = if let Ok((_, name)) = identifier(&[name]) { name } else { return Err(crate::Error::ParserError) };

    let body = match MacroBody::parse(value) {
      Ok((_, body)) => body,
      Err(_) => return Err(crate::Error::ParserError),
    };

    let value = match body {
      MacroBody::Statement(_) => return Err(crate::Error::ParserError),
      MacroBody::Expr(expr) => expr,
    };

    Ok(Self { name, value })
  }

  /// Evaluate the value and type of this macro and generate corresponding Rust code.
  pub fn generate<C>(&mut self, cx: C) -> Result<(TokenStream, Option<Type>), crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let mut ctx = LocalContext { args: HashMap::new(), export_as_macro: false, global_context: &cx };

    let ty = self.value.finish(&mut ctx)?;
    self.value.to_tokens(&mut ctx, &mut tokens);

    Ok((tokens, ty))
  }
}

/// A function-like macro.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), cmacro::Error> {
/// use cmacro::{FnMacro, CodegenContext};
///
/// // #define FUNC(a, b, c) a + b * c
/// let name = "FUNC";
/// let args = ["(", "a", ",", "b", ",", "c", ")"];
/// let value = ["a", "+", "b", "*", "c"];
///
/// let mut fn_macro = FnMacro::parse(name, &args, &value)?;
/// let output = fn_macro.generate(())?;
/// assert_eq!(
///   output.to_string(),
///   "macro_rules ! FUNC { ($ a : expr , $ b : expr , $ c : expr) => { ($ a + ($ b * $ c)) } ; }",
/// );
/// # Ok(())
/// # }
/// ```
///
/// ```
/// # fn main() -> Result<(), cmacro::Error> {
/// use cmacro::{FnMacro, CodegenContext};
///
/// struct Context;
///
/// impl CodegenContext for Context {
///   fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
///     match (macro_name, arg_name) {
///       ("FUNC", "a" | "b" | "c") => Some("u32".into()),
///       _ => None,
///     }
///   }
/// }
///
/// // #define FUNC(a, b, c) a + b * c
/// let name = "FUNC";
/// let args = ["(", "a", ",", "b", ",", "c", ")"];
/// let value = ["a", "+", "b", "*", "c"];
///
/// let mut fn_macro = FnMacro::parse(name, &args, &value)?;
/// let output = fn_macro.generate(Context)?;
/// assert_eq!(
///   output.to_string(),
///   "# [allow (non_snake_case)] # [inline (always)] pub unsafe extern \"C\" fn FUNC (mut a : u32 , mut b : u32 , mut c : u32) -> u32 { (a + (b * c)) }",
/// );
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct FnMacro {
  /// The name of this function macro.
  pub name: String,
  /// The arguments of this function macro.
  pub args: Vec<String>,
  /// The body of this function macro.
  pub body: MacroBody,
}

impl FnMacro {
  fn parse_args<I>(input: &[I]) -> IResult<&[I], Vec<String>>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter
      + Slice<RangeFrom<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + Clone,
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

  /// Parse a function-like macro from a name, arguments and body tokens.
  pub fn parse<I, C>(name: I, args: &[I], body: &[I]) -> Result<Self, crate::Error>
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
    let (_, name) = identifier(&[name]).map_err(|_| crate::Error::ParserError)?;
    let (_, args) = Self::parse_args(args).map_err(|_| crate::Error::ParserError)?;
    let (_, body) = MacroBody::parse(body).map_err(|_| crate::Error::ParserError)?;

    Ok(Self { name, args, body })
  }

  /// Infer the type of this function macro and generate corresponding Rust code.
  pub fn generate<C>(&mut self, cx: C) -> Result<TokenStream, crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let mut args = HashMap::new();
    for arg in &self.args {
      let ty = if let Some(arg_ty) = cx.macro_arg_ty(&self.name, arg) {
        MacroArgType::Known(Type::try_from(syn::parse_str::<syn::Type>(&arg_ty).unwrap())?)
      } else {
        MacroArgType::Unknown
      };

      args.insert(arg.to_owned(), ty);
    }

    let mut ctx = LocalContext { args, export_as_macro: false, global_context: &cx };
    let ret_ty = self.body.finish(&mut ctx)?;

    let export_as_macro = ctx.is_variadic() || !ctx.args.iter().all(|(_, ty)| matches!(*ty, MacroArgType::Known(_)));
    ctx.export_as_macro = export_as_macro;

    let name = Ident::new(&self.name, Span::call_site());

    let mut body = TokenStream::new();
    match &self.body {
      MacroBody::Statement(stmt) => stmt.to_tokens(&mut ctx, &mut body),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut body),
    }

    if export_as_macro {
      let args = self
        .args
        .iter()
        .map(|arg| {
          let id = Ident::new(arg, Span::call_site());
          let ty = ctx.args.get(arg).unwrap();

          if matches!(ty, MacroArgType::Ident) {
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
      let func_args = self
        .args
        .iter()
        .map(|arg| {
          if let Some(MacroArgType::Known(ty)) = ctx.args.remove(arg) {
            let id = Ident::new(arg, Span::call_site());
            let ty = ty.to_token_stream(&mut ctx);
            quote! { #id: #ty }
          } else {
            unreachable!()
          }
        })
        .collect::<Vec<_>>();

      let return_type = ret_ty.map(|ty| {
        let ty = ty.to_token_stream(&mut ctx);
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
