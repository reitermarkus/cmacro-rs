#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportREAD_PSP {
  ($pucOutCurrentStackPointer:expr) => {
    ::core::arch::asm!(
      "mrs {0}, psp",
      out(reg) $pucOutCurrentStackPointer,
      clobber_abi("C"),
    )
  };
}
pub use __cmacro__secureportREAD_PSP as secureportREAD_PSP;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__secureportSET_PSP {
  ($pucCurrentStackPointer:expr) => {
    ::core::arch::asm!(
      "msr psp, {0}",
      in(reg) $pucCurrentStackPointer,
      clobber_abi("C"),
    )
  };
}
pub use __cmacro__secureportSET_PSP as secureportSET_PSP;
