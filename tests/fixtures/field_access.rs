#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_field__ {
  ($x:expr) => {
    $x.field
  };
}
#[doc(inline)]
pub use __cmacro__access_field__ as access_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_pointer_field__ {
  ($x:expr) => {
    (*$x).field
  };
}
#[doc(inline)]
pub use __cmacro__access_pointer_field__ as access_pointer_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_renamed_field__ {
  ($x:expr) => {
    $x.new_name
  };
}
#[doc(inline)]
pub use __cmacro__access_renamed_field__ as access_renamed_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_address__ {
  ($x:expr) => {
    (*ptr::addr_of_mut!($x)).new_name
  };
}
#[doc(inline)]
pub use __cmacro__access_address__ as access_address;
