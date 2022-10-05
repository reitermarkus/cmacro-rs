macro_rules! access_field {
  ($x:expr) => {
    $x.field
  };
}

macro_rules! access_pointer_field {
  ($x:expr) => {
    (*$x).field
  };
}

macro_rules! access_renamed_field {
  ($x:expr) => {
    $x.new_name
  };
}

macro_rules! access_address {
  ($x:expr) => {
    (*ptr::addr_of_mut!($x)).new_name
  };
}
