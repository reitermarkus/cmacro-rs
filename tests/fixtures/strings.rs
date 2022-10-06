pub const s1: *const c_char = [255, 0].as_ptr() as *const c_char;

pub const s2: *const c_char = [255, 255, 0].as_ptr() as *const c_char;

pub const s3: *const c_char = [255, 255, 0].as_ptr() as *const c_char;

pub const HELLO1: *const c_char = [87, 79, 82, 76, 68, 0].as_ptr() as *const c_char;
pub const HELLO2: *const c_char = [87, 79, 82, 76, 68, 0].as_ptr() as *const c_char as *const c_char;
