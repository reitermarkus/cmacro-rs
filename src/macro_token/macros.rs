macro_rules! arg {
  ($index:expr) => {{
    $crate::MacroToken::Arg($crate::ast::MacroArg { index: $index })
  }};
}
pub(crate) use arg;

macro_rules! token {
  ($token:expr) => {{
    $crate::MacroToken::Token(::std::borrow::Cow::Owned($token.into()))
  }};
}
pub(crate) use token;

macro_rules! id {
  ($id:ident) => {{
    $crate::MacroToken::Identifier($crate::ast::Identifier { id: ::std::borrow::Cow::Borrowed(stringify!($id)) })
  }};
}
pub(crate) use id;

macro_rules! string {
  (u8 $s:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::String($crate::ast::LitString::Utf8($s.into())))
  }};
  ($s:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::String($crate::ast::LitString::Ordinary($s.as_bytes().into())))
  }};
}
pub(crate) use string;

macro_rules! char {
  (u8 $c:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Char($crate::ast::LitChar::Utf8(u8::try_from($c).unwrap())))
  }};
  (u $c:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Char($crate::ast::LitChar::Utf16(u16::try_from($c).unwrap())))
  }};
  (U $c:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Char($crate::ast::LitChar::Utf32(u32::from($c))))
  }};
  ($c:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Char($crate::ast::LitChar::Ordinary(u8::try_from($c).unwrap())))
  }};
}
pub(crate) use char;

macro_rules! int {
  (ull $value:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Int($crate::ast::LitInt {
      value: $value,
      suffix: Some($crate::ast::BuiltInType::ULongLong),
    }))
  }};
  ($value:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Int($crate::ast::LitInt { value: $value, suffix: None }))
  }};
}
pub(crate) use int;

macro_rules! double {
  ($value:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Float($crate::ast::LitFloat::Double($value)))
  }};
}
pub(crate) use double;

macro_rules! comment {
  ($comment:expr) => {{
    $crate::MacroToken::Comment($crate::ast::Comment::try_from($comment).unwrap())
  }};
}
pub(crate) use comment;

macro_rules! punct {
  ($punct:expr) => {{
    $crate::MacroToken::Punctuation($punct)
  }};
}
pub(crate) use punct;

macro_rules! tokens {
  ($($token:expr),*) => {{
    &[
      $(
        $token.into()
      ),*
    ]
  }};
}
pub(crate) use tokens;
