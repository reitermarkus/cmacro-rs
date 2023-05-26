macro_rules! lit_id {
  (@ $name:ident) => {
    $crate::ast::LitIdent { id: stringify!($name).into(), macro_arg: true }
  };
  ($name:ident) => {
    $crate::ast::LitIdent { id: stringify!($name).into(), macro_arg: false }
  };
}
pub(crate) use lit_id;

macro_rules! id {
  (@ $name:ident) => {
    $crate::ast::Identifier::Literal($crate::ast::lit_id!(@ $name))
  };
  ($name:ident) => {
    $crate::ast::Identifier::Literal($crate::ast::lit_id!($name))
  };
}
pub(crate) use id;

macro_rules! var {
  (@ $name:ident) => {
    $crate::ast::Expr::Variable { name: $crate::ast::id!(@ $name) }
  };
  ($name:ident) => {
    $crate::ast::Expr::Variable { name: $crate::ast::id!($name) }
  };
}
pub(crate) use var;

macro_rules! lit {
  (u8 $c:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::Char($crate::ast::LitChar::Utf8($c as u8)))
  };
  (u $c:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::Char($crate::ast::LitChar::Utf16($c as u16)))
  };
  (U $c:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::Char($crate::ast::LitChar::Utf32($c as u32)))
  };
  (L $c:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::Char($crate::ast::LitChar::Wide($c as u32)))
  };
  ($lit:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::from($lit))
  };
}
pub(crate) use lit;

macro_rules! ty {
  (*mut $($ty:tt)*) => { Type::Ptr { ty: Box::new($crate::ast::ty!($($ty)*)), mutable: true } };
  (*const $($ty:tt)*) => { Type::Ptr { ty: Box::new($crate::ast::ty!($($ty)*)), mutable: false } };
  (struct $ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).into()), is_struct: true } };
  ($ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).into()), is_struct: false } };
  ($ty:path) => { Type::BuiltIn($ty) };
}
pub(crate) use ty;

macro_rules! assert_eq_tokens {
  ($expr:expr, $expected:expr) => {
    let mut ctx = LocalContext {
      root_name: Default::default(),
      names: Default::default(),
      arg_types: Default::default(),
      export_as_macro: false,
      global_context: &(),
      generate_cstr: true,
      is_variable_macro: true,
    };

    let tokens = $expr.to_token_stream(&mut ctx);
    assert_eq!(tokens.to_string(), $expected.parse::<TokenStream>().unwrap().to_string());
  };
}
pub(crate) use assert_eq_tokens;
