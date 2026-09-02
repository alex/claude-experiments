//! A minimal SIMD abstraction for the byte-search kernels.
//!
//! The kernels in [`search`](crate::string::search) and
//! [`mem`](crate::string::mem) are written once,
//! generic over [`Lanes`], and instantiated for each backend by the
//! [`dispatch!`](crate::string::simd::dispatch) macro, which runs them
//! inside a function that has the backend's target features enabled.
//! Every method here is `#[inline(always)]`, so the intrinsics end up in
//! that function and compile to single instructions.
//!
//! Only the handful of operations the kernels need are provided; the
//! `Mask` type is whatever the backend produces from a byte comparison
//! (a vector of `0xff`/`0x00` bytes for SSE2/AVX2, a `k` register for
//! AVX-512), so combining several comparisons stays in the cheapest
//! domain and is converted to an integer bitmask only once.
//!
//! # Safety contract
//! The intrinsic calls are `unsafe` because the intrinsics require their
//! target feature. `dispatch!` only instantiates a backend after `cpuid`
//! confirmed the feature and inside a `#[target_feature]` function, which
//! is what makes them sound; the backends must not be used in any other
//! way.

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

/// A predicate over the lanes of a [`Lanes`] vector.
pub trait Mask: Copy {
    /// One bit per lane, lane 0 in bit 0.
    fn bits(self) -> u64;
    /// True if any lane is set.
    fn any(self) -> bool;
    /// True if every lane is set.
    fn all(self) -> bool;
    /// Lane-wise or.
    fn or(self, other: Self) -> Self;
    /// Lane-wise and.
    fn and(self, other: Self) -> Self;
    /// Lane-wise not.
    fn not(self) -> Self;
    /// `self & !other`.
    fn and_not(self, other: Self) -> Self;
}

/// A vector of `N` bytes.
pub trait Lanes: Copy {
    /// Bytes per vector.
    const N: usize;
    /// Result of a comparison.
    type Mask: Mask;
    /// Unaligned load of `N` bytes.
    ///
    /// # Safety
    /// `p` must be readable for `N` bytes.
    unsafe fn load(p: *const u8) -> Self;
    /// Unaligned store of `N` bytes.
    ///
    /// # Safety
    /// `p` must be writable for `N` bytes.
    unsafe fn store(self, p: *mut u8);
    /// Every lane set to `b`.
    fn splat(b: u8) -> Self;
    /// Lane-wise equality.
    fn eq(self, other: Self) -> Self::Mask;
    /// Lane-wise unsigned minimum.
    fn min(self, other: Self) -> Self;
    /// `self` in the lanes where `self == other`, zero elsewhere. A zero
    /// lane of the result therefore means "different, or equal and NUL":
    /// exactly where a string comparison stops. Several results combine
    /// with [`min`](Self::min) and are tested with one comparison.
    fn keep_eq(self, other: Self) -> Self;
    /// Lane-wise exclusive or.
    fn xor(self, other: Self) -> Self;
}

/// 16-byte vectors (x86_64 baseline).
#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
pub struct Sse2(__m128i);

#[cfg(target_arch = "x86_64")]
impl Mask for Sse2 {
    #[inline(always)]
    fn bits(self) -> u64 {
        // SAFETY: SSE2 is part of the x86_64 baseline.
        unsafe { _mm_movemask_epi8(self.0) as u32 as u64 }
    }
    #[inline(always)]
    fn any(self) -> bool {
        self.bits() != 0
    }
    #[inline(always)]
    fn all(self) -> bool {
        self.bits() == 0xffff
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_or_si128(self.0, other.0) })
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_and_si128(self.0, other.0) })
    }
    #[inline(always)]
    fn not(self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_xor_si128(self.0, _mm_set1_epi8(-1)) })
    }
    #[inline(always)]
    fn and_not(self, other: Self) -> Self {
        // SAFETY: baseline. (`andnot` computes `!a & b`.)
        Self(unsafe { _mm_andnot_si128(other.0, self.0) })
    }
}

#[cfg(target_arch = "x86_64")]
impl Lanes for Sse2 {
    const N: usize = 16;
    type Mask = Sse2;
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: caller contract; baseline instruction.
        Self(unsafe { _mm_loadu_si128(p as *const __m128i) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u8) {
        // SAFETY: caller contract; baseline instruction.
        unsafe { _mm_storeu_si128(p as *mut __m128i, self.0) }
    }
    #[inline(always)]
    fn splat(b: u8) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_set1_epi8(b as i8) })
    }
    #[inline(always)]
    fn eq(self, other: Self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_cmpeq_epi8(self.0, other.0) })
    }
    #[inline(always)]
    fn min(self, other: Self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_min_epu8(self.0, other.0) })
    }
    #[inline(always)]
    fn keep_eq(self, other: Self) -> Self {
        // SAFETY: baseline. Equal lanes are 0xff, so `min` keeps `self`.
        Self(unsafe { _mm_min_epu8(self.0, _mm_cmpeq_epi8(self.0, other.0)) })
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: baseline.
        Self(unsafe { _mm_xor_si128(self.0, other.0) })
    }
}

/// 32-byte vectors (AVX2).
#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
pub struct Avx2(__m256i);

#[cfg(target_arch = "x86_64")]
impl Mask for Avx2 {
    #[inline(always)]
    fn bits(self) -> u64 {
        // SAFETY: see the module documentation.
        unsafe { _mm256_movemask_epi8(self.0) as u32 as u64 }
    }
    #[inline(always)]
    fn any(self) -> bool {
        self.bits() != 0
    }
    #[inline(always)]
    fn all(self) -> bool {
        self.bits() == 0xffff_ffff
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_or_si256(self.0, other.0) })
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_and_si256(self.0, other.0) })
    }
    #[inline(always)]
    fn not(self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_xor_si256(self.0, _mm256_set1_epi8(-1)) })
    }
    #[inline(always)]
    fn and_not(self, other: Self) -> Self {
        // SAFETY: see the module documentation. (`andnot` computes `!a & b`.)
        Self(unsafe { _mm256_andnot_si256(other.0, self.0) })
    }
}

#[cfg(target_arch = "x86_64")]
impl Lanes for Avx2 {
    const N: usize = 32;
    type Mask = Avx2;
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: caller contract; see the module documentation.
        Self(unsafe { _mm256_loadu_si256(p as *const __m256i) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u8) {
        // SAFETY: caller contract; see the module documentation.
        unsafe { _mm256_storeu_si256(p as *mut __m256i, self.0) }
    }
    #[inline(always)]
    fn splat(b: u8) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_set1_epi8(b as i8) })
    }
    #[inline(always)]
    fn eq(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_cmpeq_epi8(self.0, other.0) })
    }
    #[inline(always)]
    fn min(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_min_epu8(self.0, other.0) })
    }
    #[inline(always)]
    fn keep_eq(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_min_epu8(self.0, _mm256_cmpeq_epi8(self.0, other.0)) })
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm256_xor_si256(self.0, other.0) })
    }
}

/// 64-byte vectors (AVX-512F + AVX-512BW); comparisons produce `k` masks.
#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
pub struct Avx512(__m512i);

#[cfg(target_arch = "x86_64")]
impl Mask for u64 {
    #[inline(always)]
    fn bits(self) -> u64 {
        self
    }
    #[inline(always)]
    fn any(self) -> bool {
        self != 0
    }
    #[inline(always)]
    fn all(self) -> bool {
        self == u64::MAX
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        self | other
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        self & other
    }
    #[inline(always)]
    fn not(self) -> Self {
        !self
    }
    #[inline(always)]
    fn and_not(self, other: Self) -> Self {
        self & !other
    }
}

#[cfg(target_arch = "x86_64")]
impl Lanes for Avx512 {
    const N: usize = 64;
    type Mask = u64;
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: caller contract; see the module documentation.
        Self(unsafe { _mm512_loadu_si512(p as *const _) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u8) {
        // SAFETY: caller contract; see the module documentation.
        unsafe { _mm512_storeu_si512(p as *mut _, self.0) }
    }
    #[inline(always)]
    fn splat(b: u8) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm512_set1_epi8(b as i8) })
    }
    #[inline(always)]
    fn eq(self, other: Self) -> u64 {
        // SAFETY: see the module documentation.
        unsafe { _mm512_cmpeq_epi8_mask(self.0, other.0) }
    }
    #[inline(always)]
    fn min(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm512_min_epu8(self.0, other.0) })
    }
    #[inline(always)]
    fn keep_eq(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm512_maskz_mov_epi8(_mm512_cmpeq_epi8_mask(self.0, other.0), self.0) })
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: see the module documentation.
        Self(unsafe { _mm512_xor_si512(self.0, other.0) })
    }
}

/// 16-byte NEON vectors (the AArch64 baseline). A mask is the comparison
/// result itself (`0xff`/`0x00` lanes); [`Mask::bits`] compresses it to
/// one bit per lane with a weighted horizontal add, since NEON has no
/// `movemask`.
#[cfg(target_arch = "aarch64")]
#[derive(Clone, Copy)]
pub struct Neon(uint8x16_t);

#[cfg(target_arch = "aarch64")]
impl Mask for Neon {
    #[inline(always)]
    fn bits(self) -> u64 {
        // SAFETY: NEON is always available on AArch64.
        unsafe {
            let weights = vld1q_u8(WEIGHTS.as_ptr());
            let v = vandq_u8(self.0, weights);
            let lo = vaddv_u8(vget_low_u8(v)) as u64;
            let hi = vaddv_u8(vget_high_u8(v)) as u64;
            lo | (hi << 8)
        }
    }
    #[inline(always)]
    fn any(self) -> bool {
        // SAFETY: as above.
        unsafe { vmaxvq_u8(self.0) != 0 }
    }
    #[inline(always)]
    fn all(self) -> bool {
        // SAFETY: as above.
        unsafe { vminvq_u8(self.0) != 0 }
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vorrq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vandq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn not(self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vmvnq_u8(self.0) })
    }
    #[inline(always)]
    fn and_not(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vbicq_u8(self.0, other.0) })
    }
}

/// Bit weights for [`Mask::bits`] on NEON: lane `i` contributes bit
/// `i % 8` of its half.
#[cfg(target_arch = "aarch64")]
static WEIGHTS: [u8; 16] = [1, 2, 4, 8, 16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128];

#[cfg(target_arch = "aarch64")]
impl Lanes for Neon {
    const N: usize = 16;
    type Mask = Neon;
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: caller contract.
        Neon(unsafe { vld1q_u8(p) })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u8) {
        // SAFETY: caller contract.
        unsafe { vst1q_u8(p, self.0) }
    }
    #[inline(always)]
    fn splat(b: u8) -> Self {
        // SAFETY: NEON is always available on AArch64.
        Neon(unsafe { vdupq_n_u8(b) })
    }
    #[inline(always)]
    fn eq(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vceqq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn min(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vminq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn keep_eq(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { vandq_u8(self.0, vceqq_u8(self.0, other.0)) })
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: as above.
        Neon(unsafe { veorq_u8(self.0, other.0) })
    }
}
