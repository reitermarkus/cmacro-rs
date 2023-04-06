pub const s1: &CStr = {
  const BYTES: &[u8; 2] = b"\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
};

pub const s2: &CStr = {
  const BYTES: &[u8; 3] = b"\xFF\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
};

pub const s3: &CStr = {
  const BYTES: &[u8; 3] = b"\xFF\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
};

pub const HELLO1: &CStr = {
  const BYTES: &[u8; 6] = b"WORLD\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
};
pub const HELLO2: &CStr = {
  const BYTES: &[u8; 6] = b"WORLD\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
};
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn HELLO3() -> *const c_char {
  {
    const BYTES: &[u8; 2] = b"!\0";
    BYTES.as_ptr() as *const c_char
  }
}

pub const CAST_STRING: *mut c_int = {
  const BYTES: &[u8; 10] = b"STRINGINT\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
}.as_ptr() as *mut c_int;

pub const UTF8: &[u8; 6] = b"UTF-8\0";
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF8_FN() -> *const u8 {
  {
    const BYTES: &[u8; 6] = b"UTF-8\0";
    BYTES.as_ptr()
  }
}

pub const UTF16: &[u16; 7] = &[85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 0u16];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF16_FN() -> *const u16 {
  {
    const WORDS: &[u16; 7] = &[85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 0u16];
    WORDS.as_ptr()
  }
}

pub const UTF32: &[u32; 7] = &[85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 0u32];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF32_FN() -> *const u32 {
  {
    const DWORDS: &[u32; 7] = &[85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 0u32];
    DWORDS.as_ptr()
  }
}

pub const WIDE: &[wchar_t; 5] = &[87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 0 as wchar_t];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn WIDE_FN() -> *const wchar_t {
  {
    const WCHARS: &[wchar_t; 5] = &[87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 0 as wchar_t];
    WCHARS.as_ptr()
  }
}
