//! Raw bindings to the generated assembly.

#[cfg(target_arch = "x86_64")]
extern "C" {
    /// Compress `nblocks` 64-byte blocks from `data` into `state`.
    ///
    /// Verified contract (Lean: `CC.X86.SHA256Scalar`): requires BMI1/BMI2 and
    /// MOVBE; `data` must be readable for `64 * nblocks` bytes and `state`
    /// writable for 32 bytes, and the two must not overlap.
    pub fn cc_sha256_blocks_x86_scalar(state: *mut u32, data: *const u8, nblocks: usize);
}
