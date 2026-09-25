//! Formally verified assembly implementations of cryptographic algorithms.
//!
//! Every function in this crate is a thin, safe wrapper around assembly code
//! that is generated from, and proven correct in, the Lean 4 development in
//! `claude-crypto/lean`.  The proofs establish, for the assembly itself:
//!
//! * **functional correctness** against a readable transcription of the
//!   relevant standard (FIPS 180-4 for SHA-256),
//! * **memory safety**: the code only reads its inputs and only writes its
//!   outputs and its own stack frame, and
//! * **constant time** (where relevant): control flow and memory addresses do
//!   not depend on secret data.
//!
//! See `claude-crypto/README.md` for the precise statements and the trusted
//! computing base.

#![no_std]
#![deny(missing_docs)]

mod asm;
pub mod sha256;

pub use sha256::{sha256, Sha256};
