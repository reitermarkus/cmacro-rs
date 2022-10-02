macro_rules! id {
  ($name:ident) => {
    $crate::ast::Identifier::Literal(String::from(stringify!($name)))
  };
}
pub(crate) use id;

macro_rules! var {
  ($name:ident) => {
    $crate::ast::Expr::Variable { name: id!($name) }
  };
}
pub(crate) use var;

macro_rules! lit {
  ($lit:literal) => {
    $crate::ast::Expr::Literal($crate::ast::Lit::from($lit))
  };
}
pub(crate) use lit;

macro_rules! ty {
  (*mut $($ty:tt)*) => { Type::Ptr { ty: Box::new(ty!($($ty)*)), mutable: true } };
  (*const $($ty:tt)*) => { Type::Ptr { ty: Box::new(ty!($($ty)*)), mutable: false } };
  (struct $ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).to_owned()), is_struct: true } };
  ($ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).to_owned()), is_struct: false } };
  ($ty:path) => { Type::BuiltIn($ty) };
}
pub(crate) use ty;
