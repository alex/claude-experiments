//! Raw bindings to the generated assembly.

#[cfg(target_arch = "x86_64")]
extern "C" {
    /// Compress `nblocks` 64-byte blocks from `data` into `state`.
    ///
    /// Verified contract (Lean: `CC.X86.SHA256Scalar`): requires BMI1/BMI2 and
    /// MOVBE; `data` must be readable for `64 * nblocks` bytes and `state`
    /// writable for 32 bytes, and the two must not overlap.
    pub fn cc_sha256_blocks_x86_scalar(state: *mut u32, data: *const u8, nblocks: usize);

    /// Compress `nblocks` 64-byte blocks from `data` into `state`.
    ///
    /// Verified contract (Lean: `CC.X86.SHA256Avx2.correct`): requires AVX2 and
    /// BMI1/BMI2; `data` must be readable for `64 * nblocks` bytes and `state`
    /// writable for 32 bytes, and the two must not overlap.  Uses 560 bytes of
    /// stack.
    pub fn cc_sha256_blocks_x86_avx2(state: *mut u32, data: *const u8, nblocks: usize);
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
extern "C" {
    /// Compress `nblocks` 64-byte blocks from `data` into `state`.
    ///
    /// Verified contract (Lean: `CC.Arm.SHA256Ce.correct`): requires the Armv8
    /// SHA-256 instructions (FEAT_SHA256); `data` must be readable for
    /// `64 * nblocks` bytes and `state` readable and writable for 32 bytes.
    /// Preserves all AAPCS64 callee-saved registers and uses no stack.
    pub fn cc_sha256_blocks_arm(state: *mut u32, data: *const u8, nblocks: usize);
}

#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
extern "C" {
    /// Compress `nblocks` 64-byte blocks from `data` into `state`.
    ///
    /// Verified contract (Lean: `CC.Ppc.SHA256P8.correct`): requires the
    /// POWER8 (Power ISA 2.07) vector crypto instructions, which every
    /// ppc64le (ELFv2) Linux system has; `data` must be readable for
    /// `64 * nblocks` bytes and `state` readable and writable for 32 bytes.
    /// Preserves all ELFv2 nonvolatile registers (uses only `r0`, `r3`–`r12`
    /// and `v0`–`v19`) and uses no stack and no TOC.
    pub fn cc_sha256_blocks_ppc64le(state: *mut u32, data: *const u8, nblocks: usize);
}
