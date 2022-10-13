#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__INLINE_COMMENTS {
  ($a:expr, $b:expr, $c:expr) => {
    $a % $b / $c
  };
}
pub use __cmacro__INLINE_COMMENTS as INLINE_COMMENTS;
