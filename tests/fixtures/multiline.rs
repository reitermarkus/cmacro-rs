#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__MULTILINE {
  ($a:expr, $b:expr, $c:expr) => {
    $a % $b / $c
  };
}
pub use __cmacro__MULTILINE as MULTILINE;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__MULTILINE_BRACES {
  ($a:expr) => {{
      $a;
  }};
}
pub use __cmacro__MULTILINE_BRACES as MULTILINE_BRACES;


#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__MULTILINE_BRACES_NO_INDENT {
  ($a:expr) => {{
      $a;
  }};
}
pub use __cmacro__MULTILINE_BRACES_NO_INDENT as MULTILINE_BRACES_NO_INDENT;

