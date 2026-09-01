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
//! * `nr` – the syscall number table.

#[cfg(target_arch = "x86_64")]
#[path = "x86_64/mod.rs"]
mod imp;

pub use imp::*;
