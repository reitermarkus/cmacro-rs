pub const NULL: *mut c_void = ptr::null_mut();

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__IS_NULL {
    ($ptr:expr) => {
        $ptr == ptr::null_mut()
    };
}
pub use __cmacro__IS_NULL as IS_NULL;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__IS_NONNULL {
    ($ptr:expr) => {
        $ptr != ptr::null_mut()
    };
}
pub use __cmacro__IS_NONNULL as IS_NONNULL;
