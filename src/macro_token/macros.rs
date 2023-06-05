macro_rules! double {
  ($value:expr) => {{
    $crate::MacroToken::Lit($crate::ast::Lit::Float($crate::ast::LitFloat::Double($value)))
  }};
}
pub(crate) use double;

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
