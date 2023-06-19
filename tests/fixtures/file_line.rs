pub const LINE_VAR: c_uint = line!() as c_uint;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__LINE {
  () => {
    line!() as c_uint
  };
}
pub use __cmacro__LINE as LINE;

pub const FILE_VAR: *const c_char = {
  const BYTES: &[u8] = concat!(file!(), '\0').as_bytes();
  BYTES.as_ptr() as *const c_char
};

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__FILE {
  () => {{
    const BYTES: &[u8] = concat!(file!(), '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro__FILE as FILE;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__STRINGIFY {
  ($s:expr) => {{
    const BYTES: &[u8] = concat!(stringify!($s), '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro__STRINGIFY as STRINGIFY;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__STRINGIFY2 {
  ($s:expr) => {{
    const BYTES: &[u8] = concat!(stringify!($s), '\0').as_bytes();
    BYTES.as_ptr() as * const c_char
  }};
}
pub use __cmacro__STRINGIFY2 as STRINGIFY2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__LINE_AND_FILE {
  () => {{
    const BYTES: &[u8] = concat!(file!(), stringify!(line!()), '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro__LINE_AND_FILE as LINE_AND_FILE;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__STRINGIFY_FILE {
  () => {{
    const BYTES: &[u8] = concat!(format!("{:?}", file!()), '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro__STRINGIFY_FILE as STRINGIFY_FILE;
