#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportREAD_PSP {
  ($pucOutCurrentStackPointer:expr) => {
    arch::asm!(
      "mrs {0}, psp",
      out(reg) $pucOutCurrentStackPointer,
      options(nomem, preserves_flags),
    );
  };
}
pub use __cmacro__secureportREAD_PSP as secureportREAD_PSP;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportSET_PSP {
  ($pucCurrentStackPointer:expr) => {
    arch::asm!(
      "msr psp, {0}",
      in(reg) $pucCurrentStackPointer,
      options(nomem, preserves_flags),
    );
  };
}
pub use __cmacro__secureportSET_PSP as secureportSET_PSP;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__i386_example1 {
  ($old:expr, $base:expr, $offset:expr) => {
    arch::asm!(
      "btsl {2},{1}",
      "sbb {0},{0}",
      out(reg) $old,
      inout(reg) *$base,
      in(reg) $offset,
      options(nomem),
    );
  };
}
pub use __cmacro__i386_example1 as i386_example1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__i386_example2 {
  ($src:expr, $dst:expr) => {
    arch::asm!(
      "mov {1}, {0}",
      "add $1, {0}",
      out(reg) $dst,
      in(reg) $src,
      options(att_syntax, nomem, preserves_flags),
    );
  };
}
pub use __cmacro__i386_example2 as i386_example2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__vax_example {
  ($from:expr, $to:expr, $count:expr) => {
    arch::asm!(
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

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__func {
  () => {
    arch::global_asm!(
      ".globl func",
      ".type func, @function",
      "func:",
      ".cfi_startproc",
      "movl $7, %eax",
      "ret",
      ".cfi_endproc",
      options(att_syntax),
    );
  };
}
pub use __cmacro__func as func;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__times5 {
  ($n: expr) => {
    arch::asm!(
      "leal ({0},{0},4),{0}",
      inout(reg) $n,
      options(att_syntax, nomem, preserves_flags),
    );
  };
}
pub use __cmacro__times5 as times5;
