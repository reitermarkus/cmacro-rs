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
pub(crate) struct LocalContext<'t, 'g, C> {
  pub(crate) args: HashMap<&'t str, MacroArgType>,
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g C,
}

impl<'t, 'g, C> LocalContext<'t, 'g, C> {
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

impl<C> LocalContext<'_, '_, C>
where
  C: CodegenContext,
{
  pub fn is_variable_known(&self, id: &str) -> bool {
    self.args.contains_key(id) || self.macro_variable(id).is_some()
  }
}

impl<'t, 'g, C> CodegenContext for LocalContext<'t, 'g, C>
where
  C: CodegenContext,
{
  fn function(&self, name: &str) -> Option<Vec<String>> {
    self.global_context.function(name)
  }

  fn macro_variable(&self, name: &str) -> Option<Expr> {
    self.global_context.macro_variable(name)
  }

  fn ffi_prefix(&self) -> Option<TokenStream> {
    self.global_context.ffi_prefix()
  }

  fn num_prefix(&self) -> Option<TokenStream> {
    self.global_context.num_prefix()
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

pub trait CodegenContext {
  #[allow(unused_variables)]
  fn function(&self, name: &str) -> Option<Vec<String>> {
    None
  }

  #[allow(unused_variables)]
  fn macro_variable(&self, name: &str) -> Option<Expr> {
    None
  }

  fn ffi_prefix(&self) -> Option<TokenStream> {
    None
  }

  fn num_prefix(&self) -> Option<TokenStream> {
    None
  }
}

impl CodegenContext for Context {
  fn function(&self, name: &str) -> Option<Vec<String>> {
    self.functions.get(name).cloned()
  }

  fn macro_variable(&self, name: &str) -> Option<Expr> {
    self.macro_variables.get(name).cloned()
  }

  fn ffi_prefix(&self) -> Option<TokenStream> {
    self.ffi_prefix.clone()
  }

  fn num_prefix(&self) -> Option<TokenStream> {
    self.num_prefix.clone()
  }
}
