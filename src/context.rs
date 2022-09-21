use super::*;

/// Type of a macro argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroArgType {
  /// `ident` type
  Ident,
  /// `expr` type
  Expr,
  /// known type
  Known(String),
  /// unknown type
  Unknown,
}

#[derive(Debug)]
pub struct Context<'s, 'f> {
  pub(crate) args: HashMap<&'s str, MacroArgType>,
  pub(crate) export_as_macro: bool,
  pub(crate) functions: HashMap<&'f str, Vec<String>>,
}

impl<'s, 't> Context<'s, 't> {
  pub fn is_variadic(&self) -> bool {
    self.args.contains_key("...")
  }

  pub fn arg_type_mut(&mut self, name: &str) -> Option<&mut MacroArgType> {
    self.args.get_mut(name)
  }

  pub fn is_macro_arg(&self, name: &str) -> bool {
    self.args.get(name).map(|ty| self.export_as_macro || *ty != MacroArgType::Unknown).unwrap_or(false)
  }
}
