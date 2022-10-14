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

pub(crate) struct ParseContext<'m> {
  #[allow(unused)]
  pub name: &'m str,
  pub args: &'m [&'m str],
}

impl<'m> ParseContext<'m> {
  const NO_ARGS: &'static [&'static str] = &[];

  pub const fn fn_macro(name: &'m str, args: &'m [&'m str]) -> Self {
    Self { name, args }
  }

  pub const fn var_macro(name: &'m str) -> Self {
    Self { name, args: Self::NO_ARGS }
  }
}

/// Local code generation context.
#[derive(Debug, Clone)]
pub(crate) struct LocalContext<'g, C> {
  pub(crate) root_name: String,
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

  pub fn is_variable_macro(&self) -> bool
  where
    C: context::CodegenContext,
  {
    self.variable_macro(&self.root_name).is_some()
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
      root_name: self.root_name.clone(),
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
  fn ffi_prefix(&self) -> Option<TokenStream> {
    self.global_context.ffi_prefix()
  }

  fn trait_prefix(&self) -> Option<TokenStream> {
    self.global_context.trait_prefix()
  }

  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    self.global_context.macro_arg_ty(macro_name, arg_name)
  }

  fn resolve_ty(&self, ty: &str) -> Option<String> {
    self.global_context.resolve_ty(ty)
  }

  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
    self.global_context.function(name)
  }

  fn function_macro(&self, name: &str) -> Option<&FnMacro> {
    self.global_context.function_macro(name)
  }

  fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
    self.global_context.variable_macro(name)
  }
}

/// Context for code generation.
pub trait CodegenContext {
  /// Get the prefix for FFI types, e.g. `c_char` or `c_ulong`.
  fn ffi_prefix(&self) -> Option<TokenStream> {
    None
  }

  /// Get the prefix for traits, macros and constants, e.g. `arch::asm!` or `f32::INFINITY`.
  ///
  /// Most of the time, this is either `::core::` or `::std::`.
  fn trait_prefix(&self) -> Option<TokenStream> {
    None
  }

  /// Get the type for the given macro argument.
  #[allow(unused_variables)]
  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    None
  }

  /// Resolve the given type.
  ///
  /// For example, given
  ///
  /// ```c
  /// typedef unsigned long MyType;
  /// ```
  ///
  /// is defined, this should return `Some("unsigned long".into())`
  /// when `ty` is `"MyType"`.
  #[allow(unused_variables)]
  fn resolve_ty(&self, ty: &str) -> Option<String> {
    None
  }

  /// Get the argument types and return type for the function with the given `name`.
  ///
  /// For example, given a C function
  ///
  /// ```c
  /// int add(int, int);
  /// ```
  ///
  /// exists, this should return `Some((vec!["int".into(), "int".into()], "int".into()))`
  /// when `name` is `"add"`.
  #[allow(unused_variables)]
  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
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
}

impl<T> CodegenContext for &T
where
  T: CodegenContext,
{
  fn ffi_prefix(&self) -> Option<TokenStream> {
    T::ffi_prefix(self)
  }

  fn trait_prefix(&self) -> Option<TokenStream> {
    T::trait_prefix(self)
  }

  fn macro_arg_ty(&self, macro_name: &str, arg_name: &str) -> Option<String> {
    T::macro_arg_ty(self, macro_name, arg_name)
  }

  fn resolve_ty(&self, ty: &str) -> Option<String> {
    T::resolve_ty(self, ty)
  }

  fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
    T::function(self, name)
  }

  fn function_macro(&self, name: &str) -> Option<&FnMacro> {
    T::function_macro(self, name)
  }

  fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
    T::variable_macro(self, name)
  }
}

impl CodegenContext for () {}
