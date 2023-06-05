#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access {
  ($x:expr, $field:ident) => {
    $x. $field
  };
}
pub use __cmacro__access as access;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_field {
  ($x:expr) => {
    $x.field
  };
}
pub use __cmacro__access_field as access_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_pointer_field {
  ($x:expr) => {
    (*$x).field
  };
}
pub use __cmacro__access_pointer_field as access_pointer_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_inc_pointer_field {
  ($x:expr) => {
    (*{ let prev = $x; $x = $x.add(1); prev }).field
  };
}
pub use __cmacro__access_inc_pointer_field as access_inc_pointer_field;

pub const old_name: _ = new_name;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_renamed_field {
  ($x:expr) => {
    $x.new_name
  };
}
pub use __cmacro__access_renamed_field as access_renamed_field;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__access_address {
  ($x:expr) => {
    (*ptr::addr_of_mut!($x)).new_name
  };
}
pub use __cmacro__access_address as access_address;
