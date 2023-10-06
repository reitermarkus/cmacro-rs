macro_rules! comment {
  ($comment:expr) => {{
    $crate::ast::Comment::try_from($comment).unwrap()
  }};
}
pub(crate) use comment;

macro_rules! arg {
  ($index:expr) => {
    $crate::ast::MacroArg { index: $index }
  };
}
pub(crate) use arg;

macro_rules! var {
  ($name:ident) => {
    $crate::ast::Expr::Var($crate::ast::Var { name: $crate::ast::id!($name) })
  };
}
pub(crate) use var;

macro_rules! id {
  ($name:ident) => {
    $crate::ast::Identifier { id: ::std::borrow::Cow::Borrowed(stringify!($name)) }
  };
}
pub(crate) use id;

macro_rules! id_cont {
  ($id_cont:expr) => {
    $crate::ast::IdentifierContinue::try_from($id_cont).unwrap()
  };
}
pub(crate) use id_cont;

macro_rules! lit_int {
  (ull $value:expr) => {{
    $crate::ast::Lit::Int($crate::ast::LitInt { value: $value, suffix: Some($crate::ast::BuiltInType::ULongLong) })
  }};
  ($value:expr) => {{
    $crate::ast::Lit::Int($crate::ast::LitInt { value: $value, suffix: None })
  }};
}
pub(crate) use lit_int;

macro_rules! lit_float {
  (f $value:expr) => {{
    $crate::ast::Lit::Float($crate::ast::LitFloat::Float($value))
  }};
  ($value:expr) => {{
    $crate::ast::Lit::Float($crate::ast::LitFloat::Double($value))
  }};
}
pub(crate) use lit_float;

macro_rules! lit_char {
  ($c:literal) => {
    $crate::ast::Lit::Char($crate::ast::LitChar::Ordinary(u8::try_from($c).unwrap()))
  };
  (u8 $c:literal) => {
    $crate::ast::Lit::Char($crate::ast::LitChar::Utf8(u8::try_from($c).unwrap()))
  };
  (u $c:literal) => {
    $crate::ast::Lit::Char($crate::ast::LitChar::Utf16(u16::try_from($c).unwrap()))
  };
  (U $c:literal) => {
    $crate::ast::Lit::Char($crate::ast::LitChar::Utf32(u32::try_from($c).unwrap()))
  };
  (L $c:literal) => {
    $crate::ast::Lit::Char($crate::ast::LitChar::Wide(u32::try_from($c).unwrap()))
  };
}
pub(crate) use lit_char;

macro_rules! lit_string {
  ($s:literal) => {
    $crate::ast::Lit::String($crate::ast::LitString::Ordinary($s.as_bytes().into()))
  };
  (u8 $s:literal) => {
    $crate::ast::Lit::String($crate::ast::LitString::Utf8($s.into()))
  };
  (u $s:literal) => {
    $crate::ast::Lit::String($crate::ast::LitString::Utf16($s.into()))
  };
  (U $s:literal) => {
    $crate::ast::Lit::String($crate::ast::LitString::Utf32($s.into()))
  };
  (L $words:expr) => {
    $crate::ast::Lit::String($crate::ast::LitString::Wide($words))
  };
}
pub(crate) use lit_string;

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
  (const $($ty:tt)*) => { Type::Qualified { ty: Box::new($crate::ast::ty!($($ty)*)), qualifier: $crate::ast::TypeQualifier::Const } };
  (*mut $($ty:tt)*) => { Type::Ptr { ty: Box::new($crate::ast::ty!($($ty)*)) } };
  (*const $($ty:tt)*) => { Type::Qualified { ty: Box::new(Type::Ptr { ty: Box::new($crate::ast::ty!($($ty)*)) }), qualifier: $crate::ast::TypeQualifier::Const } };
  (struct $ty:ident) => { Type::Identifier { name: Box::new($crate::ast::var!($ty)), is_struct: true } };
  ($ty:ident) => { Type::Identifier { name: Box::new($crate::ast::var!($ty)), is_struct: false } };
  ($ty:path) => { Type::BuiltIn($ty) };
}
pub(crate) use ty;

macro_rules! punct {
  ($punct:expr) => {{
    $crate::ast::Punctuation::try_from($punct).unwrap()
  }};
}
pub(crate) use punct;

macro_rules! parse_tokens {
  ($ty:ty => [$($token:expr),* $(,)?], $expr:expr $(,)?) => {{
    use nom::combinator::all_consuming;
    let tokens = $crate::macro_token::tokens![$($token),*];
    let expr = all_consuming(<$ty>::parse)(&tokens).map(|(_, expr)| expr);
    assert_eq!(expr, Ok($expr))
  }};
}
pub(crate) use parse_tokens;

macro_rules! assert_eq_tokens {
  ($expr:expr, $expected:expr) => {
    let mut ctx = LocalContext {
      arg_names: Default::default(),
      arg_types: Default::default(),
      export_as_macro: false,
      global_context: &(),
      generate_cstr: true,
      static_lifetime_elision: true,
      is_variable_macro: true,
    };

    let tokens = $expr.to_token_stream(&mut ctx);
    assert_eq!(tokens.to_string(), $expected.parse::<TokenStream>().unwrap().to_string());
  };
}
pub(crate) use assert_eq_tokens;
