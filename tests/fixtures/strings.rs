pub const s1: *const c_char = {
  const BYTES: [u8; 2] = *b"\xFF\0";
  BYTES.as_ptr() as *const c_char
};

pub const s2: *const c_char = {
  const BYTES: [u8; 3] = *b"\xFF\xFF\0";
  BYTES.as_ptr() as *const c_char
};

pub const s3: *const c_char = {
  const BYTES: [u8; 3] = *b"\xFF\xFF\0";
  BYTES.as_ptr() as *const c_char
};

pub const HELLO1: *const c_char = {
  const BYTES: [u8; 6] = *b"WORLD\0";
  BYTES.as_ptr() as *const c_char
};
pub const HELLO2: *const c_char = {
  const BYTES: [u8; 6] = *b"WORLD\0";
  BYTES.as_ptr() as *const c_char
} as *const c_char;
