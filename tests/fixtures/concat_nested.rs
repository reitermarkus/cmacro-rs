#[doc (hidden)]
#[macro_export] macro_rules! __cmacro____int_c_join {
  ($a:ident, $b:ident) => {
    concat_idents!($a, $b)
  };
}
pub use __cmacro____int_c_join as __int_c_join;

#[doc(hidden)]
#[macro_export] macro_rules! __cmacro____int_c {
  ($v:ident, $suffix:ident) => {
    concat_idents!($v, $suffix)
  };
}
pub use __cmacro____int_c as __int_c;

#[doc(hidden)]
#[macro_export] macro_rules! __cmacro____uint_c {
  ($v:ident, $suffix:ident) => {
    concat_idents!($v, U, $suffix)
  };
}
pub use __cmacro____uint_c as __uint_c;


#[doc(hidden)]
#[macro_export] macro_rules! __cmacro__UINT64_C {
  ($v:ident) => {
    concat_idents!($v, U__int64_c_suffix)
  };
}
pub use __cmacro__UINT64_C as UINT64_C;
