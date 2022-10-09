#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro____STRING__ {
  ($x:expr) => {
    concat!(stringify!($x), '\0').as_ptr() as *const c_char
  };
}
#[doc(inline)]
pub use __cmacro____STRING__ as __STRING;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__DOUBLE_STRING__ {
  ($x:expr) => {
    concat!(stringify!($x), stringify!($x), '\0').as_ptr() as *const c_char
  };
}
#[doc(inline)]
pub use __cmacro__DOUBLE_STRING__ as DOUBLE_STRING;
