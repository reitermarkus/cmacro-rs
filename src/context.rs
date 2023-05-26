use std::collections::{HashMap, HashSet};

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
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g C,
  pub(crate) generate_cstr: bool,
  pub(crate) is_variable_macro: bool,
}

impl<'g, C> LocalContext<'g, C>
where
  C: CodegenContext,
{
  pub fn new(root_name: &str, cx: &'g C) -> Self {
    let root_name = root_name.to_owned();

    let mut names = HashSet::new();
    names.insert(root_name.clone());

    Self {
      root_name,
      names,
      arg_types: Default::default(),
      export_as_macro: false,
      global_context: cx,
      generate_cstr: true,
      is_variable_macro: false,
    }
  }
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
    self.is_variable_macro
  }
}

impl<C> LocalContext<'_, C>
where
  C: CodegenContext,
{
  pub fn eval_variable(&mut self, name: &str) -> Result<(Expr, Option<Type>), crate::CodegenError> {
    if self.names.contains(name) {
      return Err(crate::CodegenError::RecursiveDefinition(name.to_owned()))
    }

    let mut ctx = Self::new(&self.root_name, self.global_context);
    ctx.names.insert(name.to_owned());
    ctx.names.extend(self.names.iter().cloned());

    if ctx.is_variable_macro() {
      return Err(crate::CodegenError::UnknownVariable(name.to_owned()))
    }

    self.export_as_macro = true;

    Ok((Expr::Variable { name: LitIdent { id: name.to_owned(), macro_arg: false } }, None))
  }
}

impl<'g, C> CodegenContext for LocalContext<'g, C>
where
  C: CodegenContext,
{
  fn rust_target(&self) -> Option<String> {
    self.global_context.rust_target()
  }

  fn ffi_prefix(&self) -> Option<syn::Path> {
    self.global_context.ffi_prefix()
  }

  fn trait_prefix(&self) -> Option<syn::Path> {
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
}

/// Context for code generation.
pub trait CodegenContext {
  /// Get the minimum Rust target to generate code for.
  fn rust_target(&self) -> Option<String> {
    None
  }

  /// Get the prefix for FFI types, e.g. `c_char` or `c_ulong`.
  fn ffi_prefix(&self) -> Option<syn::Path> {
    None
  }

  /// Get the prefix for traits, macros and constants, e.g. `arch::asm!` or `f32::INFINITY`.
  ///
  /// Most of the time, this is either `::core::` or `::std::`.
  fn trait_prefix(&self) -> Option<syn::Path> {
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
}

impl<T> CodegenContext for &T
where
  T: CodegenContext,
{
  fn rust_target(&self) -> Option<String> {
    T::rust_target(self)
  }

  fn ffi_prefix(&self) -> Option<syn::Path> {
    T::ffi_prefix(self)
  }

  fn trait_prefix(&self) -> Option<syn::Path> {
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
}

impl CodegenContext for () {}
