use std::{fmt::Debug, str};

use proc_macro2::TokenStream;
use quote::TokenStreamExt;
use semver::{Version, VersionReq};

use crate::{ast::Lit, is_identifier, CodegenContext, Expr, LocalContext, MacroBody, MacroToken};

/// A variable-like macro.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use cmacro::{MacroSet, VarMacro};
///
/// let mut macro_set = MacroSet::new();
///
/// // #define VAR 4 + 7 + 82
/// macro_set.define_var_macro("VAR", &["4", "+", "7", "*", "82"]);
///
/// let body = macro_set.expand_var_macro("VAR")?;
/// let mut var_macro = VarMacro::parse("VAR", &body)?;
///
/// let (output, ty) = var_macro.generate(())?;
/// assert_eq!(output.to_string(), "578");
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct VarMacro<'t> {
  name: String,
  body: MacroBody<'t>,
}

impl<'t> VarMacro<'t> {
  /// Parse a variable-like macro from a name and value tokens.
  pub fn parse(name: &str, value: &[MacroToken<'t>]) -> Result<Self, crate::ParserError> {
    let name = if is_identifier(name) { name.to_owned() } else { return Err(crate::ParserError::InvalidMacroName) };

    let body = match MacroBody::parse(value) {
      Ok((_, body)) => body,
      Err(_) => return Err(crate::ParserError::InvalidMacroBody),
    };

    Ok(Self { name, body })
  }

  /// Evaluate the value and type of this macro and generate corresponding Rust code.
  pub fn generate<C>(&mut self, cx: C) -> Result<(TokenStream, Option<TokenStream>), crate::CodegenError>
  where
    C: CodegenContext,
  {
    let mut ctx = LocalContext::new(&cx);
    ctx.is_variable_macro = true;

    ctx.generate_cstr = ctx
      .rust_target()
      .and_then(|v| {
        let version = Version::parse(&v).ok()?;
        let req = VersionReq::parse(">=1.59").unwrap();
        Some(req.matches(&version))
      })
      .unwrap_or(true);

    let mut tokens = TokenStream::new();

    if matches!(self.body, MacroBody::Statement(_)) {
      ctx.export_as_macro = true;
    }

    // Cannot generate non-expression variable-like macros.
    let value = self.value_mut().ok_or(crate::CodegenError::NonExpressionVarMacro)?;

    let ty = value.finish(&mut ctx)?;

    // TODO: Move this special case into `LitString::finish`.
    let ty = if let Expr::Literal(Lit::String(ref lit)) = value {
      let (ty, s) = lit.to_token_stream(&mut ctx, true);
      tokens.append_all(s);
      Some(ty)
    } else {
      value.to_tokens(&mut ctx, &mut tokens);
      ty.map(|ty| ty.to_token_stream(&mut ctx))
    };

    Ok((tokens, ty))
  }

  /// The name of this variable macro.
  pub fn name(&self) -> &str {
    &self.name
  }

  /// The value of this variable macro.
  pub fn value(&self) -> Option<&Expr> {
    match &self.body {
      MacroBody::Statement(_) => None,
      MacroBody::Expr(expr) => Some(expr),
    }
  }

  pub(crate) fn value_mut(&mut self) -> Option<&mut Expr<'t>> {
    match &mut self.body {
      MacroBody::Statement(_) => None,
      MacroBody::Expr(expr) => Some(expr),
    }
  }
}
