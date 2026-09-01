//! `<string.h>`: memory and string functions.
//!
//! * [`mem`] – `memcpy`, `memmove`, `memset`, `memcmp` and friends,
//! * [`str`] – the `str*` family,
//! * [`simd`] – runtime SIMD level selection used by both.

pub mod mem;
pub mod simd;
pub mod str;
