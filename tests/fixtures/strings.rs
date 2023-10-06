pub const s1: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"\xFF\0") }
};

pub const s2: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"\xFF\xFF\0") }
};

pub const s3: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"\xFF\xFF\0") }
};

pub const HELLO1: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"WORLD\0") }
};
pub const HELLO2: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"WORLD\0") }
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
  BYTES.as_ptr() as *const c_char
} as *mut c_int;

pub const UTF8: &[u8; 6] = b"UTF-8\0";
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF8_FN() -> *const u8 {
  {
    const BYTES: &[u8; 6] = b"UTF-8\0";
    BYTES.as_ptr()
  }
}

pub const UTF8_CONCAT: &[u8; 20] = b"UTF-8 and then some\0";
pub const UTF8_CONCAT_UTF8: &[u8; 20] = b"UTF-8 and then some\0";

pub const UTF16: &[u16; 7] = &[85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 0u16];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF16_FN() -> *const u16 {
  {
    const WORDS: &[u16; 7] = &[85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 0u16];
    WORDS.as_ptr()
  }
}

pub const UTF16_CONCAT: &[u16; 20] = &[
  85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 97u16, 110u16, 100u16, 32u16, 116u16, 104u16, 101u16, 110u16, 32u16, 115u16, 111u16, 109u16, 101u16, 0u16,
];
pub const UTF16_CONCAT_UTF16: &[u16; 20] = &[
  85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 97u16, 110u16, 100u16, 32u16, 116u16, 104u16, 101u16, 110u16, 32u16, 115u16, 111u16, 109u16, 101u16, 0u16,
];

pub const UTF32: &[u32; 7] = &[85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 0u32];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn UTF32_FN() -> *const u32 {
  {
    const DWORDS: &[u32; 7] = &[85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 0u32];
    DWORDS.as_ptr()
  }
}

pub const UTF32_CONCAT: &[u32; 20] = &[
    85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 97u32, 110u32, 100u32, 32u32, 116u32, 104u32, 101u32, 110u32, 32u32, 115u32, 111u32, 109u32, 101u32, 0u32,
];
pub const UTF32_CONCAT_UTF32: &[u32; 20] = &[
    85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 97u32, 110u32, 100u32, 32u32, 116u32, 104u32, 101u32, 110u32, 32u32, 115u32, 111u32, 109u32, 101u32, 0u32,
];

pub const WIDE: &[wchar_t; 5] = &[87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 0 as wchar_t];
#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn WIDE_FN() -> *const wchar_t {
  {
    const WCHARS: &[wchar_t; 5] = &[87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 0 as wchar_t];
    WCHARS.as_ptr()
  }
}

pub const WIDE_CONCAT: &[wchar_t; 18] = &[
  87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 97 as wchar_t, 110 as wchar_t, 100 as wchar_t, 32 as wchar_t, 116 as wchar_t, 104 as wchar_t, 101 as wchar_t, 110 as wchar_t, 32 as wchar_t, 115 as wchar_t, 111 as wchar_t, 109 as wchar_t, 101 as wchar_t, 0 as wchar_t,
];
pub const WIDE_CONCAT_WIDE: &[wchar_t; 18] = &[
  87 as wchar_t, 73 as wchar_t, 68 as wchar_t, 69 as wchar_t, 97 as wchar_t, 110 as wchar_t, 100 as wchar_t, 32 as wchar_t, 116 as wchar_t, 104 as wchar_t, 101 as wchar_t, 110 as wchar_t, 32 as wchar_t, 115 as wchar_t, 111 as wchar_t, 109 as wchar_t, 101 as wchar_t, 0 as wchar_t,
];

pub const ORDINARY_BANANA1: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"a\xE7\x8C\xAB\xF0\x9F\x8D\x8C\0") }
};
pub const ORDINARY_BANANA2: &CStr = {
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(b"a\xE7\x8C\xAB\xF0\x9F\x8D\x8C\0") }
};

pub const UTF8_BANANA1: &[u8; 9] = b"a\xE7\x8C\xAB\xF0\x9F\x8D\x8C\0";
pub const UTF8_BANANA2: &[u8; 9] = b"a\xE7\x8C\xAB\xF0\x9F\x8D\x8C\0";

pub const UTF16_BANANA1: &[u16; 5] = &[97u16, 29483u16, 55356u16, 57164u16, 0u16];
pub const UTF16_BANANA2: &[u16; 5] = &[97u16, 29483u16, 55356u16, 57164u16, 0u16];

pub const UTF32_BANANA1: &[u32; 4] = &[97u32, 29483u32, 127820u32, 0u32];
pub const UTF32_BANANA2: &[u32; 4] = &[97u32, 29483u32, 127820u32, 0u32];

pub const WIDE_BANANA1: &[wchar_t; 4] = &[97 as wchar_t, 29483 as wchar_t, 127820 as wchar_t, 0 as wchar_t];
pub const WIDE_BANANA2: &[wchar_t; 4] = &[97 as wchar_t, 29483 as wchar_t, 127820 as wchar_t, 0 as wchar_t];

pub const INTERIOR_NULL_BYTE: &[u8; 4] = b"a\0b\0";
