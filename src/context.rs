use super::*;

/// Type of a macro argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MacroArgType {
  /// `ident` type
  Ident,
  /// `expr` type
  Expr,
  /// known type
  Known(Type),
  /// unknown type
  Unknown,
}

/// Local code generation context.
#[derive(Debug)]
pub(crate) struct LocalContext<'g, C> {
  pub(crate) args: HashMap<String, MacroArgType>,
  pub(crate) arg_values: HashMap<String, &'g Expr>,
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
    self.args.get(name).is_some()
  }
}

impl<C> LocalContext<'_, C>
where
  C: CodegenContext,
{
  pub fn is_variable_known(&self, id: &str) -> bool {
    self.args.contains_key(id) || self.variable_macro(id).is_some()
  }

  pub fn variable_macro_value(&self, name: &str) -> Option<&Expr> {
    self
      .arg_values
      .get(name)
      .map(|expr| *expr)
      .or_else(|| CodegenContext::variable_macro(self, name).map(|var_macro| &var_macro.value))
  }
}

impl<'g, C> CodegenContext for LocalContext<'g, C>
where
  C: CodegenContext,
{
  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
    self.global_context.function(name)
  }

  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    self.global_context.macro_arg_ty(macro_name, arg_name)
  }

  fn resolve_ty(&self, ty: &str) -> Option<String> {
    self.global_context.resolve_ty(ty)
  }

  fn function_macro(&self, name: &str) -> Option<&FnMacro> {
    self.global_context.function_macro(name)
  }

  fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
    self.global_context.variable_macro(name)
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
  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
    None
  }

  /// Get the type for the given macro argument.
  #[allow(unused_variables)]
  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    None
  }

  /// Resolve the given type.
  #[allow(unused_variables)]
  fn resolve_ty(&self, ty: &str) -> Option<String> {
    None
  }

  /// Get the parsed function-like macro with the given `name`.
  #[allow(unused_variables)]
  fn function_macro(&self, name: &str) -> Option<&FnMacro> {
    None
  }

  /// Get the parsed variable-like macro with the given `name`.
  #[allow(unused_variables)]
  fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
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
  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
    T::function(self, name)
  }

  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    T::macro_arg_ty(self, macro_name, arg_name)
  }

  fn resolve_ty(&self, ty: &str) -> Option<String> {
    T::resolve_ty(self, ty)
  }

  fn function_macro(&self, name: &str) -> Option<&FnMacro> {
    T::function_macro(self, name)
  }

  fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
    T::variable_macro(self, name)
  }

  fn ffi_prefix(&self) -> Option<TokenStream> {
    T::ffi_prefix(self)
  }

  fn num_prefix(&self) -> Option<TokenStream> {
    T::num_prefix(self)
  }
}

impl CodegenContext for () {}
