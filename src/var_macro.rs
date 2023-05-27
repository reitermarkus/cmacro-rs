use std::{fmt::Debug, str};

use proc_macro2::TokenStream;
use quote::TokenStreamExt;
use semver::{Version, VersionReq};

use crate::{
  ast::Lit, is_identifier, CodegenContext, Expr, LocalContext, MacroBody, MacroToken, ParseContext,
};

/// A variable-like macro.
///
/// # Examples
///
/// ```ignore
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
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
  name: String,
  body: MacroBody,
}

impl VarMacro {
  /// Parse a variable-like macro from a name and value tokens.
  pub fn parse(name: &str, value: &[MacroToken<'_>]) -> Result<Self, crate::ParserError> {
    let name = if is_identifier(name) { name.to_owned() } else { return Err(crate::ParserError::InvalidMacroName) };

    let ctx = ParseContext::var_macro(&name);
    let body = match MacroBody::parse(value, &ctx) {
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
    let mut ctx = LocalContext::new(&self.name, &cx);
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

  pub(crate) fn value_mut(&mut self) -> Option<&mut Expr> {
    match &mut self.body {
      MacroBody::Statement(_) => None,
      MacroBody::Expr(expr) => Some(expr),
    }
  }
}
