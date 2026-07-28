//! Kani proof harnesses for the `self_cell` crate.
//!
//! `self_cell` builds safe self-referential structs on top of a small block of
//! hand-written `unsafe` code (`self_cell::unsafe_self_cell`). That code hand
//! rolls a heap allocation holding an `Owner` and a `Dependent` side by side,
//! manual field-by-field drop ordering, and panic-safety drop guards.
//!
//! These harnesses drive the *public* API and let Kani discharge the memory
//! safety and behavioural obligations bit-precisely, for all values of a
//! nondeterministic input, rather than for the handful of concrete values a
//! unit test happens to pick.
//!
//! Everything is gated on `cfg(kani)` so that a plain `cargo build` of this
//! crate is a no-op.

#[cfg(kani)]
mod tracking;

#[cfg(kani)]
mod construct_drop;
#[cfg(kani)]
mod data_integrity;
#[cfg(kani)]
mod fallible;
#[cfg(kani)]
mod into_owner;
#[cfg(kani)]
mod mut_borrow;
#[cfg(kani)]
mod pointer_stability;
