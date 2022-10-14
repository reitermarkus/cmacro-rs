#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__F {
  () => {
    777
  };
}
pub use __cmacro__F as F;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__ARG_CALL {
  ($F:expr) => {
    $F()
  };
}
pub use __cmacro__ARG_CALL as ARG_CALL;
