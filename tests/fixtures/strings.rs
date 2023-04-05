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

pub const CAST_STRING: *mut c_int = {
  const BYTES: &[u8; 10] = b"STRINGINT\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(BYTES) }
}.as_ptr() as *mut c_int;

pub const UTF8: &[u8; 6] = b"UTF-8\0";

pub const UTF16: &[u16; 7] = &[85u16, 84u16, 70u16, 45u16, 49u16, 54u16, 0u16];

pub const UTF32: &[u32; 7] = &[85u32, 84u32, 70u32, 45u32, 51u32, 50u32, 0u32];

pub const WIDE: &[wchar_t; 5] = &[87, 73, 68, 69, 0];
