pub const MY_UL: _ = 1;
pub const MY_ULL: _ = 1;

pub const MY_U_L: _ = 1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__UL {
  ($X:ident) => {
    concat_idents!($X, UL)
  };
}
pub use __cmacro__UL as UL;
pub const ONE: _ = 1;
