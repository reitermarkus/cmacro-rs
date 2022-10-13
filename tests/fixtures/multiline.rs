#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__MULTILINE {
  ($a:expr, $b:expr, $c:expr) => {
    $a % $b / $c
  };
}
pub use __cmacro__MULTILINE as MULTILINE;
