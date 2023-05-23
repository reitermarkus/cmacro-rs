#[doc(hidden)]
#[macro_export] macro_rules! __cmacro__USBD_UsrLog {
  ($($__VA_ARGS__:expr),*) => {{
    printf($($__VA_ARGS__),*);
    printf({
      const BYTES: &[u8; 2] = b"\n\0";
      BYTES.as_ptr() as * const c_char
    });
  }};
}
pub use __cmacro__USBD_UsrLog as USBD_UsrLog;
