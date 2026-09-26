//! ECDSA signature verification over the NIST P-384 curve (FIPS 186-5).
//!
//! The verifier is the assembly generated from the limb-level program
//! `CC.P384.main` of the Lean development (compiled by the verified limb-IR
//! compilers to x86-64, AArch64 and ppc64le); its specification is
//! `CC.Spec.P384.verify`: the public key is validated (both coordinates
//! `< p` and on the curve), `r` and `s` must lie in `[1, n − 1]`, and the
//! signature is checked with `e` = the 48-byte digest as a big-endian integer
//! (FIPS 186-5 §6.4.2; no truncation is needed for 384-bit digests such as
//! SHA-384).
//!
//! ECDSA verification only involves public data, so the verifier is not (and
//! need not be) constant time.
//!
//! No unverified fallback is provided: on platforms or CPUs without a
//! verified implementation, [`Verifier::new`] and [`verify`] return
//! [`Unsupported`].

use core::fmt;

/// The verified P-384 implementation is not available on this platform or CPU.
///
/// It is available on AArch64 (little-endian), on ppc64le, and on x86-64 CPUs
/// with BMI2 and MOVBE (Intel Haswell and AMD Excavator/Zen, and later).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Unsupported;

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("no verified P-384 implementation for this platform/CPU")
    }
}

/// A handle showing that the verified P-384 verifier can run on this CPU.
///
/// Obtain it once with [`Verifier::new`]; [`Verifier::verify`] then returns a
/// plain `bool`.
#[derive(Clone, Copy, Debug)]
pub struct Verifier {
    _private: (),
}

impl Verifier {
    /// Checks (once) that the verified implementation is usable here.
    pub fn new() -> Result<Self, Unsupported> {
        if is_supported() {
            Ok(Verifier { _private: () })
        } else {
            Err(Unsupported)
        }
    }

    /// Verifies the ECDSA-P384 signature `sig = r ‖ s` (two 48-byte
    /// big-endian integers) of the 48-byte message digest `digest` under the
    /// public key `pubkey = x ‖ y` (the affine coordinates, 48-byte
    /// big-endian each, i.e. the SEC 1 uncompressed encoding without the
    /// leading `0x04`).  Returns `true` iff the signature is valid; invalid
    /// public keys and out-of-range `r`, `s` are rejected.
    #[inline]
    pub fn verify(&self, pubkey: &[u8; 96], digest: &[u8; 48], sig: &[u8; 96]) -> bool {
        // SAFETY: the three pointers are valid for reads of 96, 48 and 96
        // bytes (they come from references to arrays of those sizes), which
        // is the verified contract of the assembly; it writes only its own
        // stack frame (at most 1872 bytes, including saved registers).  The CPU
        // requirements were checked when `self` was created.
        #[cfg(target_arch = "x86_64")]
        {
            unsafe { crate::asm::cc_p384_verify_x86_bmi2(pubkey.as_ptr(), digest.as_ptr(), sig.as_ptr()) == 1 }
        }
        #[cfg(all(target_arch = "aarch64", target_endian = "little"))]
        {
            unsafe { crate::asm::cc_p384_verify_aarch64(pubkey.as_ptr(), digest.as_ptr(), sig.as_ptr()) == 1 }
        }
        #[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
        {
            unsafe { crate::asm::cc_p384_verify_ppc64le(pubkey.as_ptr(), digest.as_ptr(), sig.as_ptr()) == 1 }
        }
        #[cfg(not(any(
            target_arch = "x86_64",
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "powerpc64", target_endian = "little")
        )))]
        {
            let _ = (pubkey, digest, sig);
            unreachable!("a Verifier cannot be constructed on this platform")
        }
    }
}

/// Whether the verified implementation can run on this CPU.
#[inline]
pub fn is_supported() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        // BMI2 (`mulx`) and MOVBE; the `Bmi2` level also implies BMI1.
        crate::cpu::x86_level() != crate::cpu::X86Level::Baseline
    }
    #[cfg(any(
        all(target_arch = "aarch64", target_endian = "little"),
        all(target_arch = "powerpc64", target_endian = "little")
    ))]
    {
        true
    }
    #[cfg(not(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_endian = "little"),
        all(target_arch = "powerpc64", target_endian = "little")
    )))]
    {
        false
    }
}

/// Verifies an ECDSA-P384 signature (see [`Verifier::verify`] for the
/// encodings): `Ok(true)` if valid, `Ok(false)` if invalid, and
/// `Err(Unsupported)` if the verified implementation cannot run here.
#[inline]
pub fn verify(pubkey: &[u8; 96], digest: &[u8; 48], sig: &[u8; 96]) -> Result<bool, Unsupported> {
    Ok(Verifier::new()?.verify(pubkey, digest, sig))
}
