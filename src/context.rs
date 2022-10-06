use std::collections::HashSet;

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
#[derive(Debug, Clone)]
pub(crate) struct LocalContext<'g, C> {
  pub(crate) names: HashSet<String>,
  pub(crate) arg_types: HashMap<String, MacroArgType>,
  pub(crate) arg_values: HashMap<String, &'g Expr>,
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g C,
}

impl<'g, C> LocalContext<'g, C> {
  pub fn is_variadic(&self) -> bool {
    self.arg_types.contains_key("...")
  }

  pub fn arg_type(&self, name: &str) -> Option<&MacroArgType> {
    self.arg_types.get(name)
  }

  pub fn arg_type_mut(&mut self, name: &str) -> Option<&mut MacroArgType> {
    self.arg_types.get_mut(name)
  }

  pub fn is_macro_arg(&self, name: &str) -> bool {
    self.arg_types.get(name).is_some()
  }

  pub fn is_variable_macro(&self) -> bool {
    self.arg_types.is_empty() && self.arg_values.is_empty()
  }
}

impl<C> LocalContext<'_, C>
where
  C: CodegenContext,
{
  pub fn arg_value(&self, name: &str) -> Option<&Expr> {
    self.arg_values.get(name).copied()
  }

  pub fn eval_variable(&self, name: &str) -> Result<(Expr, Option<Type>), crate::Error> {
    if self.names.contains(name) {
      return Err(crate::Error::RecursiveDefinition(name.to_owned()))
    }

    let mut names = self.names.clone();
    names.insert(name.to_owned());

    let mut ctx = Self {
      names,
      arg_types: Default::default(),
      arg_values: Default::default(),
      export_as_macro: false,
      global_context: self.global_context,
    };

    match self.variable_macro(name).map(|var_macro| var_macro.value.clone()) {
      Some(mut expr) => {
        let ty = expr.finish(&mut ctx)?;
        Ok((expr, ty))
      },
      None => Err(crate::Error::UnknownVariable(name.to_owned())),
    }
  }

  pub fn variable_macro_value(&self, name: &str) -> Option<&Expr> {
    self.variable_macro(name).map(|var_macro| &var_macro.value)
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
