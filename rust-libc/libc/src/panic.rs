//! Panic handler for the freestanding build.
//!
//! A panic inside the libc is always a bug (all inputs from C are validated
//! explicitly), so we report it on stderr and abort the process.

use core::panic::PanicInfo;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut buf = crate::sys::StderrWriter;
    let _ = core::fmt::write(&mut buf, format_args!("rustlibc: internal panic: {info}\n"));
    crate::exit::abort_now()
}

/// The prebuilt `core` library for `*-linux-gnu` targets is compiled with
/// unwinding enabled and carries a reference to this symbol. We build with
/// `panic = "abort"`, so it can never be called; it only has to exist.
#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {
    crate::exit::abort_now()
}
