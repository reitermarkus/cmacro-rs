pub const OK: _ = 0;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__IS_OK {
  ($val:expr) => {
    if $val == 0 { true } else { false }
  };
}
pub use __cmacro__IS_OK as IS_OK;
