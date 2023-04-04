//! A library for parsing C macros.
//!
//! This crate allows parsing C macros and converting them to Rust code.
//!
//! Both function-like macros (e.g. `#define FUNC(a, b, c) a + b * c`) as well
//! as variable-like macros (e.g. `#define VAR 4 + 7 * 82`) are supported.
//!
//! See [`FnMacro`] and [`VarMacro`] on how to parse macros.

#![warn(missing_debug_implementations)]
#![warn(missing_docs)]

use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
  str,
};

use nom::{
  branch::alt,
  combinator::{all_consuming, map, opt},
  multi::fold_many0,
  sequence::{preceded, terminated, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

pub mod ast;
pub use ast::*;
mod expand;
pub use expand::expand;
mod error;
pub use error::*;
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

    let ctx = ParseContext::var_macro(&name);
    let body = match MacroBody::parse(value, &ctx) {
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
  pub fn generate<C>(&mut self, cx: C) -> Result<(TokenStream, Option<TokenStream>), crate::Error>
  where
    C: CodegenContext,
  {
    let mut ctx = LocalContext::new(&self.name, &cx);

    let mut tokens = TokenStream::new();
    let ty = self.value.finish(&mut ctx)?;
    self.value.to_tokens(&mut ctx, &mut tokens);

    // TODO: Move this special case into `LitString::finish`.
    let ty = if let Expr::Literal(Lit::String(_)) = self.value {
      let ffi_prefix = ctx.trait_prefix().map(|trait_prefix| quote! { #trait_prefix ffi:: });
      Some(quote! { & #ffi_prefix CStr })
    } else {
      ty.map(|ty| ty.to_token_stream(&mut ctx))
    };

    Ok((tokens, ty))
  }
}

/// A function-like macro.
///
/// # Examples
///
/// The following example uses `()` as `CodegenContext` for simplicity,
/// therefore the argument types cannot be inferred and the macro is
/// generated as a Rust macro.
///
/// ```
/// # fn main() -> Result<(), cmacro::Error> {
/// use cmacro::{FnMacro, CodegenContext};
/// use quote::quote;
///
/// // #define FUNC(a, b, c) a + b * c
/// let name = "FUNC";
/// let args = ["a", "b", "c"];
/// let value = ["a", "+", "b", "*", "c"];
///
/// let mut fn_macro = FnMacro::parse(name, &args, &value)?;
/// let output = fn_macro.generate(())?;
/// assert_eq!(
///   output.to_string(),
///   quote! {
///     #[doc(hidden)]
///     #[macro_export]
///     macro_rules! __cmacro__FUNC {
///       ($a:expr, $b:expr, $c:expr) => {
///         $a + $b * $c
///       };
///     }
///     pub use __cmacro__FUNC as FUNC;
///   }.to_string(),
/// );
/// # Ok(())
/// # }
/// ```
///
/// When implementing a custom [`CodegenContext`] providing information on
/// the argument types of the macro using the [`CodegenContext::macro_arg_ty`] method,
/// the return type may be inferred if the macro is pure. The same is true if all types,
/// variables and functions can be resolved using the [`CodegenContext::resolve_ty`],
/// [`CodegenContext::variable_macro`], [`CodegenContext::function`] or
/// [`CodegenContext::function_macro`] methods, respectively. If all types can be inferred,
/// a function is generated instead of a macro, as seen in the following example:
///
/// ```
/// # fn main() -> Result<(), cmacro::Error> {
/// use cmacro::{FnMacro, CodegenContext};
/// use quote::quote;
///
/// struct Context;
///
/// impl CodegenContext for Context {
///   fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
///     match (macro_name, arg_name) {
///       ("FUNC", "a" | "b" | "c") => Some("unsigned int".into()),
///       _ => None,
///     }
///   }
/// }
///
/// // #define FUNC(a, b, c) a + b * c
/// let name = "FUNC";
/// let args = ["a", "b", "c"];
/// let value = ["a", "+", "b", "*", "c"];
///
/// let mut fn_macro = FnMacro::parse(name, &args, &value)?;
/// let output = fn_macro.generate(Context)?;
/// assert_eq!(
///   output.to_string(),
///   quote! {
///     #[allow(non_snake_case, unused_mut, unsafe_code)]
///     #[inline(always)]
///     pub unsafe extern "C" fn FUNC(mut a: c_uint, mut b: c_uint, mut c: c_uint) -> c_uint {
///       a + b * c
///     }
///   }.to_string(),
/// );
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
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
    all_consuming(terminated(
      alt((
        map(preceded(meta, token("...")), |var_arg| vec![var_arg.to_owned()]),
        map(
          tuple((
            fold_many0(preceded(meta, identifier), Vec::new, |mut acc, arg| {
              acc.push(arg);
              acc
            }),
            preceded(meta, opt(map(token("..."), |var_arg| var_arg.to_owned()))),
          )),
          |(arguments, var_arg)| {
            let mut arguments = arguments.to_vec();

            if let Some(var_arg) = var_arg {
              arguments.push(var_arg);
            }

            arguments
          },
        ),
      )),
      meta,
    ))(input)
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

    let ctx_args = args.iter().map(|a| a.as_str()).collect::<Vec<_>>();
    let ctx = ParseContext::fn_macro(&name, &ctx_args);
    let (_, body) = MacroBody::parse(body, &ctx).map_err(|_| crate::Error::ParserError)?;

    Ok(Self { name, args, body })
  }

  pub(crate) fn call<C>(
    mut self,
    root_name: &str,
    names: &HashSet<String>,
    args: &[Expr],
    ctx: &LocalContext<C>,
  ) -> Result<MacroBody, crate::Error>
  where
    C: CodegenContext,
  {
    if ctx.names.contains(&self.name) {
      return Err(crate::Error::RecursiveDefinition(self.name))
    }

    let mut names = names.clone();
    names.insert(self.name.clone());

    let arg_values = self.args.into_iter().zip(args.iter()).collect();
    let mut ctx = LocalContext::new_with_args(root_name, arg_values, ctx.global_context);

    self.body.finish(&mut ctx)?;

    Ok(self.body)
  }

  /// Infer the type of this function macro and generate corresponding Rust code.
  pub fn generate<C>(&mut self, cx: C) -> Result<TokenStream, crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let arg_types = self
      .args
      .iter()
      .map(|arg| {
        let ty = if let Some(arg_ty) = cx.macro_arg_ty(&self.name, arg) {
          MacroArgType::Known(arg_ty.parse()?)
        } else {
          MacroArgType::Unknown
        };

        Ok((arg.to_owned(), ty))
      })
      .collect::<Result<_, _>>()?;

    let mut ctx = LocalContext::new(&self.name, &cx);
    ctx.arg_types = arg_types;
    let ret_ty = self.body.finish(&mut ctx)?;

    ctx.export_as_macro = ctx.export_as_macro
      || (ctx.function(&self.name).is_some() && ctx.function_macro(&self.name).is_some())
      || ctx.is_variadic()
      || !ctx.arg_types.iter().all(|(_, ty)| matches!(*ty, MacroArgType::Known(_)))
      || ret_ty.is_none();

    let name = Ident::new(&self.name, Span::call_site());

    let mut body = TokenStream::new();
    match &self.body {
      MacroBody::Statement(stmt) => stmt.to_tokens(&mut ctx, &mut body),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut body),
    }

    if ctx.export_as_macro {
      let args = self
        .args
        .iter()
        .map(|arg| {
          if arg == "..." {
            quote! { $($__VA_ARGS__:expr),* }
          } else {
            let id = Ident::new(arg, Span::call_site());
            let ty = ctx.arg_type(arg).unwrap();

            if matches!(ty, MacroArgType::Ident) {
              quote! { $#id:ident }
            } else {
              quote! { $#id:expr }
            }
          }
        })
        .collect::<Vec<_>>();

      let macro_id = Ident::new(&format!("__cmacro__{}", self.name), Span::call_site());

      tokens.append_all(quote! {
        #[doc(hidden)]
        #[macro_export]
        macro_rules! #macro_id {
          (#(#args),*) => {
            #body
          };
        }
        pub use #macro_id as #name;
      })
    } else {
      let func_args = self
        .args
        .iter()
        .map(|arg| {
          if let Some(MacroArgType::Known(ty)) = ctx.arg_types.remove(arg) {
            let id = Ident::new(arg, Span::call_site());
            let ty = ty.to_token_stream(&mut ctx);
            quote! { #id: #ty }
          } else {
            unreachable!()
          }
        })
        .collect::<Vec<_>>();

      let return_type = ret_ty.and_then(|ty| {
        if ty.is_void() {
          return None
        }

        let ty = ty.to_token_stream(&mut ctx);
        Some(quote! { -> #ty })
      });

      let semicolon = if return_type.is_none() { Some(quote! { ; }) } else { None };

      tokens.append_all(quote! {
        #[allow(non_snake_case, unused_mut, unsafe_code)]
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
