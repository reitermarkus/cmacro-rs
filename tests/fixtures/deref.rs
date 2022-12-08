pub const FLASH_SIZE_DATA_REGISTER: uint32_t = 536835552u32 as uint32_t;

#[allow(non_snake_case, unused_mut)]
#[inline(always)]
pub unsafe extern "C" fn FLASH_SIZE2() -> uint16_t {
  *(536835552u32 as uint32_t as *mut uint16_t)
}
