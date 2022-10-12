#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro____CONCAT {
  ($a:expr, $b:ident, $c:ident) => {{
    const BYTES: &[u8] = concat!($a, concat_idents!($b, $c), '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro____CONCAT as __CONCAT;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__CONCAT__ {
  ($a:ident, $b:ident, $c:expr) => {{
    const BYTES: &[u8] = concat!(concat_idents!($a, $b), $c, '\0').as_bytes();
    BYTES.as_ptr() as *const c_char
  }};
}
pub use __cmacro__CONCAT__ as CONCAT__;
