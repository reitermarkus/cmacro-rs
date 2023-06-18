#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__VOID_CAST {
  ($x:expr) => {
    { let _ = $x; }
  };
}
pub use __cmacro__VOID_CAST as VOID_CAST;
