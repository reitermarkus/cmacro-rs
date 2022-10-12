#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro____STRING {
  ($x:expr) => {
    concat!(stringify!($x), '\0').as_ptr() as *const c_char
  };
}
pub use __cmacro____STRING as __STRING;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__DOUBLE_STRING {
  ($x:expr) => {
    concat!(stringify!($x), stringify!($x), '\0').as_ptr() as *const c_char
  };
}
pub use __cmacro__DOUBLE_STRING as DOUBLE_STRING;
