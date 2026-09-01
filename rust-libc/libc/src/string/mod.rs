//! `<string.h>`: memory and string functions.
//!
//! * [`mem`] – `memcpy`, `memmove`, `memset`, `memcmp` and friends,
//! * [`str`] – the `str*` family,
//! * [`search`] – the SIMD search/compare kernels behind both,
//! * [`simd`] – runtime SIMD level selection and dispatch,
//! * [`ctype`] – `<ctype.h>`.

pub mod ctype;
pub mod mem;
pub mod search;
pub mod simd;
pub mod str;
