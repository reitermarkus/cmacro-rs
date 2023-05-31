use std::{fmt::Debug, str};

use nom::{
  branch::alt,
  combinator::{all_consuming, map, opt},
  multi::fold_many0,
  sequence::{preceded, terminated, tuple},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use crate::{
  ast::{macro_id, meta, punct},
  is_identifier, CodegenContext, LocalContext, MacroArgType, MacroBody, MacroToken, Type,
};

/// A function-like macro.
///
/// # Examples
///
/// The following example uses `()` as `CodegenContext` for simplicity,
/// therefore the argument types cannot be inferred and the macro is
/// generated as a Rust macro.
///
/// ```ignore
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use cmacro::{FnMacro, CodegenContext};
/// use quote::quote;
///
/// // #define FUNC(a, b, c) a + b * c
/// let name = "FUNC";
/// let args = ["a", "b", "c"];
/// let value = ["$a", "+", "$b", "*", "$c"];
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
/// ```ignore
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
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
/// let value = ["$a", "+", "$b", "*", "$c"];
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
pub struct FnMacro<'t> {
  name: String,
  args: Vec<String>,
  body: MacroBody<'t>,
}

impl<'t> FnMacro<'t> {
  fn parse_args<'i>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Vec<String>> {
    all_consuming(terminated(
      alt((
        map(preceded(meta, punct("...")), |var_arg| vec![var_arg.to_owned()]),
        map(
          tuple((
            fold_many0(preceded(meta, macro_id), Vec::new, |mut acc, arg| {
              acc.push(arg.id.into_owned());
              acc
            }),
            preceded(meta, opt(map(punct("..."), |var_arg| var_arg.to_owned()))),
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
  pub fn parse(name: &str, args: &[MacroToken<'t>], body: &[MacroToken<'t>]) -> Result<Self, crate::ParserError> {
    let name = if is_identifier(name) { name.to_owned() } else { return Err(crate::ParserError::InvalidMacroName) };

    let (_, args) = Self::parse_args(args).map_err(|_| crate::ParserError::InvalidMacroArgs)?;

    let (_, body) = MacroBody::parse(body).map_err(|_err| crate::ParserError::InvalidMacroBody)?;

    Ok(Self { name, args, body })
  }

  /// Infer the type of this function macro and generate corresponding Rust code.
  pub fn generate<C>(&mut self, cx: C) -> Result<TokenStream, crate::CodegenError>
  where
    C: CodegenContext,
  {
    let mut tokens = TokenStream::new();

    let arg_types = self
      .args
      .iter()
      .map(|arg| {
        let ty = if let Some(arg_ty) = cx.macro_arg_ty(&self.name, arg) {
          MacroArgType::Known(Type::from_rust_ty(&arg_ty, cx.ffi_prefix().as_ref())?)
        } else {
          MacroArgType::Unknown
        };

        Ok(ty)
      })
      .collect::<Result<_, _>>()?;

    let mut ctx = LocalContext::new(&cx);
    ctx.arg_names = self.args.clone();
    ctx.arg_types = arg_types;
    let ret_ty = self.body.finish(&mut ctx)?;

    ctx.export_as_macro = ctx.export_as_macro
      || ctx.function(&self.name).is_some()
      || ctx.is_variadic()
      || !ctx.arg_types.iter().all(|ty| matches!(*ty, MacroArgType::Known(_)))
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
        .enumerate()
        .map(|(index, arg)| {
          if arg == "..." {
            quote! { $($__VA_ARGS__:expr),* }
          } else {
            let id = Ident::new(arg, Span::call_site());
            let ty = ctx.arg_type(index);

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
        .enumerate()
        .map(|(index, name)| {
          if let MacroArgType::Known(ty) = ctx.arg_type(index).clone() {
            let id = Ident::new(name, Span::call_site());
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

  /// The name of this function macro.
  pub fn name(&self) -> &str {
    &self.name
  }

  /// The arguments of this function macro.
  pub fn args(&self) -> &[String] {
    &self.args
  }

  /// The body of this function macro.
  pub fn body(&self) -> &MacroBody {
    &self.body
  }
}
