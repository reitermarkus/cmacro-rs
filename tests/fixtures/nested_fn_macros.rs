macro_rules! f1 {
  ($x:expr) => {
    ($x * 2)
  };
}

macro_rules! f2 {
  ($y:expr) => {
    ($y * ($y * 2))
  };
}
