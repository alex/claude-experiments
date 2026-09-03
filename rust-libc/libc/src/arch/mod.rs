//! Architecture specific code.
//!
//! Everything in here is the *only* assembly in the library. Each
//! architecture module must provide:
//!
//! * `syscall0` … `syscall6` – raw system calls,
//! * `_start` – the ELF entry point, which calls
//!   [`crate::start::start_c`] with the initial stack pointer,
//! * `thread_pointer()` / `set_thread_pointer()` – TLS register access,
//! * `cpu::detect()` – SIMD feature detection,
//! * `nr` – the syscall number table,
//! * `va` – `va_list` access and the `variadic_stub!` macro,
//! * `fenv` – the `<fenv.h>` functions.

#[cfg(target_arch = "x86_64")]
#[path = "x86_64/mod.rs"]
mod imp;

#[cfg(target_arch = "aarch64")]
#[path = "aarch64/mod.rs"]
mod imp;

/// Binary128 conversions (used by AArch64; tested everywhere).
#[cfg(any(target_arch = "aarch64", test))]
pub mod f128;

pub use imp::*;
