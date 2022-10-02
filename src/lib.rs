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
  mem,
  ops::{RangeFrom, RangeTo},
  str,
};

use nom::{
  branch::alt,
  combinator::{all_consuming, map, opt},
  multi::fold_many0,
  sequence::{preceded, tuple},
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
  pub fn generate<C>(&mut self, cx: C) -> Result<(TokenStream, Option<TokenStream>), crate::Error>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let mut ctx = LocalContext { args: HashMap::new(), export_as_macro: false, global_context: &cx };

    let ty = self.value.finish(&mut ctx)?;
    self.value.to_tokens(&mut ctx, &mut tokens);
    let ty = ty.map(|ty| ty.to_token_stream(&mut ctx));

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
/// let args = ["a", "b", "c"];
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
/// let args = ["a", "b", "c"];
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
    all_consuming(alt((
      map(token("..."), |var_arg| vec![var_arg.to_owned()]),
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
    )))(input)
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
        let arg_ty = syn::parse_str::<syn::Type>(&arg_ty).unwrap();
        MacroArgType::Known(Type::try_from(arg_ty)?)
      } else {
        MacroArgType::Unknown
      };

      args.insert(arg.to_owned(), ty);
    }

    let mut ctx = LocalContext { args, export_as_macro: false, global_context: &cx };
    let ret_ty = self.body.finish(&mut ctx)?;

    let export_as_macro =
      ctx.is_variadic() || !ctx.args.iter().all(|(_, ty)| matches!(*ty, MacroArgType::Known(_))) || ret_ty.is_none();
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

      let return_type = ret_ty.and_then(|ty| {
        if ty.is_void() {
          return None
        }

        let ty = ty.to_token_stream(&mut ctx);
        Some(quote! { -> #ty })
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

/// Interpolate macros in other macros.
///
/// ```
/// use std::collections::HashMap;
///
/// use cmacro::interpolate_var_macros;
///
/// let var_macros = HashMap::from([
///   ("A", vec!["1"]),
///   ("B", vec!["2"]),
///   ("PLUS", vec!["A", "+", "B"]),
///   ("CONCAT", vec!["A", "##", "B"]),
///   ("STRINGIFY", vec!["#", "A"]),
/// ]);
///
/// let fn_macros = HashMap::new();
///
/// let plus = interpolate_var_macros("PLUS", None, var_macros.get("PLUS").unwrap(), &var_macros, &fn_macros);
/// assert_eq!(plus, vec!["1", "+", "2"]);
///
/// let concat = interpolate_var_macros("CONCAT", None, var_macros.get("CONCAT").unwrap(), &var_macros, &fn_macros);
/// assert_eq!(concat, vec!["A", "##", "B"]);
///
/// let stringify = interpolate_var_macros("STRINGIFY", None, var_macros.get("STRINGIFY").unwrap(), &var_macros, &fn_macros);
/// assert_eq!(stringify, vec!["#", "A"]);
/// ```
pub fn interpolate_var_macros<'t>(
  macro_name: &str,
  macro_args: Option<&HashMap<&'t str, Option<&[&'t str]>>>,
  tokens: &[&'t str],
  var_macros: &HashMap<&str, Vec<&'t str>>,
  fn_macros: &HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
) -> Vec<&'t str> {
  fn interpolate_var_macros_inner<'t>(
    start_name: &str,
    macro_name: &str,
    macro_args: Option<&HashMap<&'t str, Option<&[&'t str]>>>,
    tokens: &[&'t str],
    var_macros: &HashMap<&str, Vec<&'t str>>,
    fn_macros: &HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
  ) -> Vec<&'t str> {
    let mut output = vec![];

    let mut it = tokens.iter().peekable();

    while let Some(token) = it.next() {
      if let Some(tokens) = macro_args.and_then(|args| args.get(token)) {
        if let Some(tokens) = tokens {
          output.extend(*tokens);
        } else {
          output.push(*token);
        }

        continue
      }

      // Don't interpolate self or function-like macro arguments.
      if *token == start_name || *token == macro_name {
        output.push(*token);
        continue
      }

      // Don't interpolate stringification or identifier concatenation.
      if *token == "#" || *token == "##" {
        output.push(token);
        if let Some(token) = it.next() {
          output.push(token);
        }

        continue
      }

      // Don't interpolate identifier concatenation.
      if it.peek() == Some(&&"##") {
        output.push(token);
        continue
      }

      if let Some((fn_args, tokens)) = fn_macros.get(token) {
        let mut paren_level = 0;

        let mut args = vec![];

        let mut jt = it.clone();
        let mut arg = vec![];

        for token in &mut jt {
          if *token == "(" {
            if paren_level != 0 {
              arg.push(*token);
            }

            paren_level += 1;
          } else if *token == ")" {
            paren_level -= 1;

            if paren_level == 0 {
              args.push(mem::take(&mut arg));
            } else {
              arg.push(*token);
            }
          } else if *token == "," && paren_level == 1 {
            args.push(mem::take(&mut arg))
          } else {
            arg.push(*token);
          }

          if paren_level == 0 {
            break
          }
        }

        if args.len() == fn_args.len() {
          let args = args
            .into_iter()
            .map(|arg| interpolate_var_macros_inner(start_name, token, None, &arg, var_macros, fn_macros))
            .collect::<Vec<_>>();

          let args = fn_args
            .iter()
            .zip(args.iter())
            .map(|(&name, arg)| (name, Some(arg.as_slice())))
            .collect::<HashMap<&str, Option<&[&str]>>>();

          it = jt;
          output.extend(interpolate_var_macros_inner(start_name, token, Some(&args), tokens, var_macros, fn_macros));
          continue
        }
      }

      if let Some(tokens) = var_macros.get(token) {
        output.extend(interpolate_var_macros_inner(start_name, token, None, tokens, var_macros, fn_macros))
      } else {
        output.push(token);
      }
    }

    output
  }

  interpolate_var_macros_inner(macro_name, macro_name, macro_args, tokens, var_macros, fn_macros)
}

/// Expand macros.
///
/// ```
/// use std::collections::HashMap;
///
/// use cmacro::expand_macros;
///
/// let mut var_macros = HashMap::from([
///   ("A", vec!["1"]),
///   ("B", vec!["2"]),
///   ("PLUS", vec!["A", "+", "B"]),
///   ("A_TIMES_B", vec!["TIMES", "(", "A", ",", "B", ")"]),
/// ]);
///
/// let mut fn_macros = HashMap::from([
///   ("TIMES", (vec!["A", "B"], vec!["A", "*", "B"])),
///   ("TIMES_B", (vec!["A"], vec!["A", "*", "B"])),
/// ]);
///
/// expand_macros(&mut var_macros, &mut fn_macros);
/// let expanded_var_macros = HashMap::from([
///   ("A", vec!["1"]),
///   ("B", vec!["2"]),
///   ("PLUS", vec!["1", "+", "2"]),
///   ("A_TIMES_B", vec!["1", "*", "2"]),
/// ]);
/// let expanded_fn_macros = HashMap::from([
///   ("TIMES", (vec!["A", "B"], vec!["A", "*", "B"])),
///   ("TIMES_B", (vec!["A"], vec!["A", "*", "2"])),
/// ]);
/// assert_eq!(var_macros, expanded_var_macros);
/// assert_eq!(fn_macros, expanded_fn_macros);
/// ```
pub fn expand_macros<'t>(
  var_macros: &mut HashMap<&str, Vec<&'t str>>,
  fn_macros: &mut HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
) {
  // Interpolate variable macros in variable macros.
  let var_macro_names = var_macros.keys().cloned().collect::<Vec<_>>();
  for macro_name in var_macro_names {
    let tokens = var_macros.get(macro_name).unwrap();
    let tokens = interpolate_var_macros(macro_name, None, tokens, var_macros, fn_macros);
    var_macros.insert(macro_name, tokens);
  }

  // Interpolate variable macros in function macros.
  let fn_macro_names = fn_macros.keys().cloned().collect::<Vec<_>>();
  for macro_name in fn_macro_names {
    let (args, tokens) = fn_macros.remove(macro_name).unwrap();
    let arg_names =
      args.iter().zip(args.iter()).map(|(&arg, _)| (arg, None)).collect::<HashMap<&str, Option<&[&str]>>>();
    let tokens = interpolate_var_macros(macro_name, Some(&arg_names), &tokens, var_macros, fn_macros);
    fn_macros.insert(macro_name, (args, tokens));
  }
}
