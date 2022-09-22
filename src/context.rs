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

/// Local code generation context.
#[derive(Debug)]
pub struct LocalContext<'t, 'g> {
  pub(crate) args: HashMap<&'t str, MacroArgType>,
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g Context,
}

impl<'t, 'g> LocalContext<'t, 'g> {
  pub fn is_variadic(&self) -> bool {
    self.args.contains_key("...")
  }

  pub fn is_variable_known(&self, id: &str) -> bool {
    self.args.contains_key(id) || self.global_context.variables.contains_key(id)
  }

  pub fn arg_type_mut(&mut self, name: &str) -> Option<&mut MacroArgType> {
    self.args.get_mut(name)
  }

  pub fn is_macro_arg(&self, name: &str) -> bool {
    self.args.get(name).map(|ty| self.export_as_macro || *ty != MacroArgType::Unknown).unwrap_or(false)
  }

  pub fn macro_variable(&self, name: &str) -> Option<&Expr> {
    self.global_context.macro_variables.get(name)
  }

  pub fn function(&self, name: &str) -> Option<&Vec<String>> {
    self.global_context.functions.get(name)
  }
}

/// Global code generation context.
#[derive(Debug, Default)]
pub struct Context {
  pub functions: HashMap<String, Vec<String>>,
  pub variables: HashMap<String, String>,
  pub macro_variables: HashMap<String, Expr>,
  pub ffi_prefix: Option<TokenStream>,
  pub num_prefix: Option<TokenStream>,
}

impl Context {
  pub fn add_var_macro(&mut self, var_macro: VarMacro) {
    self.macro_variables.insert(var_macro.name, var_macro.expr);
  }
}
