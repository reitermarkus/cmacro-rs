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
  pub(crate) arg_names: Vec<String>,
  pub(crate) arg_types: Vec<MacroArgType>,
  pub(crate) export_as_macro: bool,
  pub(crate) global_context: &'g C,
  pub(crate) generate_cstr: bool,
  pub(crate) is_variable_macro: bool,
}

impl<'g, C> LocalContext<'g, C>
where
  C: CodegenContext,
{
  pub fn new(cx: &'g C) -> Self {
    Self {
      arg_names: Default::default(),
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
    self.arg_names.last().map(|s| s.as_str()) == Some("...")
  }

  pub fn arg_name(&self, index: usize) -> &str {
    &self.arg_names[index]
  }

  pub fn arg_type(&self, index: usize) -> &MacroArgType {
    &self.arg_types[index]
  }

  pub fn arg_type_mut(&mut self, index: usize) -> &mut MacroArgType {
    &mut self.arg_types[index]
  }

  pub fn is_variable_macro(&self) -> bool
  where
    C: context::CodegenContext,
  {
    self.is_variable_macro
  }
}

impl<C> LocalContext<'_, C> where C: CodegenContext {}

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

  fn function(&self, name: &str) -> Option<(Vec<syn::Type>, syn::Type)> {
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
  fn function(&self, name: &str) -> Option<(Vec<syn::Type>, syn::Type)> {
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

  fn function(&self, name: &str) -> Option<(Vec<syn::Type>, syn::Type)> {
    T::function(self, name)
  }
}

impl CodegenContext for () {}
