//! rustlibc: a statically linked Linux libc written in Rust.
//!
//! The crate is built as a freestanding static library (`libc.a`) and
//! exports the C ABI. It talks only to the stable Linux kernel ABI.
//!
//! # Layout
//!
//! * [`arch`]   – the few pieces of per-architecture assembly: raw syscalls,
//!   `_start`, thread pointer access, CPU feature detection.
//! * [`sys`]    – typed wrappers over every syscall the library uses.
//! * [`thread`] – the thread control block (TCB), static TLS and threads.
//! * [`start`]  – process startup (`_start` → `main`) and [`exit`].
//! * [`string`] – `mem*`/`str*`.
//!
//! # Testing
//!
//! Pure functions are unit tested on the host with `cargo test`. In that
//! configuration the crate is built *with* `std` and none of the C symbols
//! are exported (`#[cfg_attr(not(test), unsafe(no_mangle))]`), so the tests
//! never shadow the host libc. End-to-end behaviour is covered by the C
//! programs under `tests/c`, which are linked against the real `libc.a`.
// `c_char` is `u8` on AArch64, which makes the `*const c_char -> *const u8`
// casts the x86_64 build needs no-ops there.
#![cfg_attr(target_arch = "aarch64", allow(clippy::unnecessary_cast))]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(test, allow(dead_code, unused_imports))]
#![allow(non_camel_case_types)]
// This crate *is* the implementation of memcpy/memset/…: LLVM must never
// recognise a loop in here as one of them and emit a (recursive) call.
#![no_builtins]

pub mod arch;
pub mod compat;
pub mod dirent;
pub mod dl;
pub mod errno;
pub mod exit;
pub mod extra;
pub mod fmt;
pub mod fnmatch;
pub mod fs;
pub mod getopt;
pub mod iconv;
pub mod locale;
pub mod malloc;
pub mod math;
pub mod misc;
pub mod poll;
pub mod process;
pub mod pwd;
pub mod resolv;
pub mod search;
pub mod signal;
pub mod socket;
pub mod start;
pub mod stdio;
pub mod stdlib;
pub mod string;
pub mod sync;
pub mod sys;
pub mod syslog;
pub mod termios;
pub mod thread;
pub mod threads;
pub mod time;
pub mod unistd;
pub mod vdso;
pub mod wchar;

#[cfg(not(test))]
mod panic;

/// Convenience alias for the C `char` type.
pub type c_char = core::ffi::c_char;
/// Convenience alias for the C `int` type.
pub type c_int = core::ffi::c_int;

/// Compile-time layout checks for the structures shared with C and the
/// kernel.  `tests/c/abi.c` asserts the same numbers from the headers.
mod abi_asserts {
    use core::mem::size_of;
    #[cfg(target_arch = "x86_64")]
    const _: () = assert!(size_of::<crate::fs::Stat>() == 144);
    #[cfg(target_arch = "aarch64")]
    const _: () = assert!(size_of::<crate::fs::Stat>() == 128);
    const _: () = assert!(size_of::<crate::fs::Rlimit>() == 16);
    const _: () = assert!(size_of::<crate::fs::Utsname>() == 390);
    const _: () = assert!(size_of::<crate::signal::SigSet>() == 128);
    const _: () = assert!(size_of::<crate::signal::SigAction>() == 152);
    const _: () = assert!(size_of::<crate::signal::StackT>() == 24);
    const _: () = assert!(size_of::<crate::time::Tm>() == 56);
    const _: () = assert!(size_of::<crate::time::Timeval>() == 16);
    const _: () = assert!(size_of::<crate::sys::Timespec>() == 16);
    const _: () = assert!(size_of::<crate::dirent::Dirent>() == 280);
    const _: () = assert!(size_of::<crate::socket::AddrInfo>() == 48);
    const _: () = assert!(size_of::<crate::socket::SockaddrIn>() == 16);
    const _: () = assert!(size_of::<crate::socket::SockaddrIn6>() == 28);
    const _: () = assert!(size_of::<crate::socket::Hostent>() == 32);
    const _: () = assert!(size_of::<crate::poll::PollFd>() == 8);
    const _: () = assert!(size_of::<crate::poll::FdSet>() == 128);
    #[cfg(target_arch = "x86_64")]
    const _: () = assert!(size_of::<crate::poll::EpollEvent>() == 12);
    #[cfg(target_arch = "aarch64")]
    const _: () = assert!(size_of::<crate::poll::EpollEvent>() == 16);
    const _: () = assert!(size_of::<crate::pwd::Passwd>() == 48);
    const _: () = assert!(size_of::<crate::pwd::Group>() == 32);
    const _: () = assert!(size_of::<crate::locale::Lconv>() == 96);
    const _: () = assert!(size_of::<crate::dl::DlPhdrInfo>() == 64);
    const _: () = assert!(size_of::<crate::termios::Termios>() == 60);
    const _: () = assert!(size_of::<crate::search::Entry>() == 16);
    const _: () = assert!(size_of::<crate::search::HsearchData>() == 16);
    const _: () = assert!(size_of::<crate::thread::sync::Mutex>() == 16);
    const _: () = assert!(size_of::<crate::thread::sync::Cond>() == 16);
    const _: () = assert!(size_of::<crate::thread::sync::RwLock>() == 16);
    const _: () = assert!(size_of::<crate::thread::sync::Barrier>() == 16);
    const _: () = assert!(size_of::<crate::thread::sync::Sem>() == 16);
    const _: () = assert!(size_of::<crate::wchar::MbState>() == 4);
}
