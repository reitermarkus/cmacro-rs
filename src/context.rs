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
pub(crate) struct LocalContext<'g, C> {
  pub(crate) args: HashMap<String, MacroArgType>,
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g C,
}

impl<'g, C> LocalContext<'g, C> {
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

impl<C> LocalContext<'_, C>
where
  C: CodegenContext,
{
  pub fn is_variable_known(&self, id: &str) -> bool {
    self.args.contains_key(id) || self.macro_variable(id).is_some()
  }
}

impl<'g, C> CodegenContext for LocalContext<'g, C>
where
  C: CodegenContext,
{
  fn function(&self, name: &str) -> Option<(Vec<String>, Type)> {
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

/// Context for code generation.
pub trait CodegenContext {
  /// Get the argument types and return type for the function with the given `name`.
  #[allow(unused_variables)]
  fn function(&self, name: &str) -> Option<(Vec<String>, Type)> {
    None
  }

  /// Get the parsed macro with the given `name`.
  #[allow(unused_variables)]
  fn macro_variable(&self, name: &str) -> Option<Expr> {
    None
  }

  /// Get the prefix for `ffi` types, e.g. `c_int`.
  fn ffi_prefix(&self) -> Option<TokenStream> {
    None
  }

  /// Get the prefix for number types, e.g. `f32`.
  fn num_prefix(&self) -> Option<TokenStream> {
    None
  }
}

impl<T> CodegenContext for &T
where
  T: CodegenContext,
{
  fn function(&self, name: &str) -> Option<(Vec<String>, Type)> {
    T::function(self, name)
  }

  fn macro_variable(&self, name: &str) -> Option<Expr> {
    T::macro_variable(self, name)
  }

  fn ffi_prefix(&self) -> Option<TokenStream> {
    T::ffi_prefix(self)
  }

  fn num_prefix(&self) -> Option<TokenStream> {
    T::num_prefix(self)
  }
}

impl CodegenContext for () {}
