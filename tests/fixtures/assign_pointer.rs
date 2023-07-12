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
