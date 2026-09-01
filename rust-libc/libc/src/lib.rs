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
#![cfg_attr(not(test), no_std)]
#![cfg_attr(test, allow(dead_code, unused_imports))]
#![allow(non_camel_case_types)]
// This crate *is* the implementation of memcpy/memset/…: LLVM must never
// recognise a loop in here as one of them and emit a (recursive) call.
#![no_builtins]

pub mod arch;
pub mod dirent;
pub mod errno;
pub mod exit;
pub mod fmt;
pub mod fs;
pub mod getopt;
pub mod malloc;
pub mod misc;
pub mod poll;
pub mod process;
pub mod pwd;
pub mod signal;
pub mod socket;
pub mod start;
pub mod stdio;
pub mod stdlib;
pub mod string;
pub mod sync;
pub mod sys;
pub mod thread;
pub mod time;
pub mod unistd;

#[cfg(not(test))]
mod panic;

/// Convenience alias for the C `char` type.
pub type c_char = core::ffi::c_char;
/// Convenience alias for the C `int` type.
pub type c_int = core::ffi::c_int;
