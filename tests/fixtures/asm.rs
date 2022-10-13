#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportREAD_PSP {
  ($pucOutCurrentStackPointer:expr) => {
    asm!(
      "mrs {0}, psp",
      out(reg) $pucOutCurrentStackPointer,
      clobber_abi("C"),
      options(nomem, preserves_flags),
    )
  };
}
pub use __cmacro__secureportREAD_PSP as secureportREAD_PSP;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportSET_PSP {
  ($pucCurrentStackPointer:expr) => {
    asm!(
      "msr psp, {0}",
      in(reg) $pucCurrentStackPointer,
      clobber_abi("C"),
      options(nomem, preserves_flags),
    )
  };
}
pub use __cmacro__secureportSET_PSP as secureportSET_PSP;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__i386_example1 {
  ($old:expr, $base:expr, $offset:expr) => {
    asm!(
      "btsl {2},{1}",
      "sbb {0},{0}",
      out(reg) $old,
      inout(reg) *$base,
      in(reg) $offset,
      clobber_abi("C"),
      options(nomem),
    );
  };
}
pub use __cmacro__i386_example1 as i386_example1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__i386_example2 {
  ($src:expr, $dst:expr) => {
    asm!(
      "mov {1}, {0}",
      "add $1, {0}",
      out(reg) $dst,
      in(reg) $src,
      clobber_abi("C"),
      options(nomem, preserves_flags),
    );
  };
}
pub use __cmacro__i386_example2 as i386_example2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__vax_example {
  ($from:expr, $to:expr, $count:expr) => {
    asm!(
      "movc3 {0}, {1}, {2}",
      in(reg) $from,
      in(reg) $to,
      in(reg) $count,
      out("r0") _,
      out("r1") _,
      out("r2") _,
      out("r3") _,
      out("r4") _,
      out("r5") _,
      clobber_abi("C") ,
      options(preserves_flags),
    );
  };
}
pub use __cmacro__vax_example as vax_example;
