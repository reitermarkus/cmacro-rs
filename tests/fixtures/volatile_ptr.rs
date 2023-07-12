#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn ASSIGN() {
  {
    let value = 42;
    ptr::write_volatile(3736059631u32 as *mut c_int, value);
    value
  };
}

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn ADD_ASSIGN() {
  {
    let value = ptr::read_volatile(3736059631u32 as *mut c_int) + 42;
    ptr::write_volatile(3736059631u32 as *mut c_int, value);
    value
  };
}

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn INC() {
  {
    let value = ptr::read_volatile(3736059631u32 as *mut c_int) + 1;
    ptr::write_volatile(3736059631u32 as *mut c_int, value);
    value
  };
}

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn POST_INC() {
  {
    let value = ptr::read_volatile(3736059631u32 as *mut c_int);
    ptr::write_volatile(3736059631u32 as *mut c_int, value + 1);
    value
  };
}

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn DEC() {
  {
    let value = ptr::read_volatile(3736059631u32 as *mut c_int) - 1;
    ptr::write_volatile(3736059631u32 as *mut c_int, value);
    value
  };
}

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn POST_DEC() {
  {
    let value = ptr::read_volatile(3736059631u32 as *mut c_int);
    ptr::write_volatile(3736059631u32 as *mut c_int, value - 1);
    value
  };
}
