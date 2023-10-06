#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn portYIELD() {
  {
    {
      let value = 268435456;
      ptr::write_volatile(3758157060u32 as *mut uint32_t, value);
      value
    };
    arch::asm!("dsb", options(nomem, preserves_flags),);
    arch::asm!("isb", options(nomem, preserves_flags),);
  };
}
pub const portNVIC_PENDSVSET_BIT: _ = 268435456;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__portEND_SWITCHING_ISR {
  ($xSwitchRequired:expr) => {
    loop { if $xSwitchRequired != pdFALSE { { let value = 268435456;
    ptr::write_volatile(3758157060u32 as * mut uint32_t, value); value };
    arch::asm!("dsb", options(nomem, preserves_flags),); arch::asm!("isb",
    options(nomem, preserves_flags),); } if 0 != 0 { continue } break }
  };
}
pub use __cmacro__portEND_SWITCHING_ISR as portEND_SWITCHING_ISR;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__portYIELD_FROM_ISR {
  ($x:expr) => {
    loop { if $x != pdFALSE { { let value = 268435456;
    ptr::write_volatile(3758157060u32 as * mut uint32_t, value); value };
    arch::asm!("dsb", options(nomem, preserves_flags),); arch::asm!("isb",
    options(nomem, preserves_flags),); } if 0 != 0 { continue } break }
  };
}
pub use __cmacro__portYIELD_FROM_ISR as portYIELD_FROM_ISR;
