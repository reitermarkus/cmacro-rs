pub const s1: &CStr = {
  const BYTES: [u8; 2] = *b"\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
};

pub const s2: &CStr = {
  const BYTES: [u8; 3] = *b"\xFF\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
};

pub const s3: &CStr = {
  const BYTES: [u8; 3] = *b"\xFF\xFF\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
};

pub const HELLO1: &CStr = {
  const BYTES: [u8; 6] = *b"WORLD\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
};
pub const HELLO2: &CStr = {
  const BYTES: [u8; 6] = *b"WORLD\0";
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
};

pub const CAST_STRING: *mut c_int = {
  const BYTES: [u8; 10] = *b"STRINGINT\0" ;
  #[allow(unsafe_code)]
  unsafe { CStr::from_bytes_with_nul_unchecked(&BYTES) }
}.as_ptr() as *mut c_int;
