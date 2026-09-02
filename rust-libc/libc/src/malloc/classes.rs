//! Size classes.
//!
//! Sizes up to 128 bytes use 16-byte steps; above that there are four
//! classes per power of two (so the worst-case internal fragmentation is
//! 25%). Every class size is a multiple of 16, and a class in the range
//! `[2^k, 2^(k+1))` is a multiple of `2^(k-2)`, which is what lets
//! `memalign` be implemented by rounding the size up to the alignment
//! (see [`class_for_aligned`]).

/// Number of size classes.
pub const NUM_CLASSES: usize = 60;

/// Largest size served from spans; anything bigger is a direct mapping.
/// Like glibc's (dynamic) mmap threshold this is large enough that the
/// working set of most programs never pays for a system call per
/// allocation.
pub const MAX_SMALL: usize = 1024 * 1024;

/// Block size of every class, in bytes.
pub const CLASS_SIZE: [u32; NUM_CLASSES] = build_table();

/// `ceil(2^44 / CLASS_SIZE[c])`: `(off * CLASS_INV[c]) >> 44` equals
/// `off / CLASS_SIZE[c]` for every `off < 2^22` (the largest span), which
/// replaces a division on the free path. Proof: with `d = CLASS_SIZE[c]`,
/// the product is `off / d + off * e / 2^44` for some `0 < e <= 1`, and
/// the error term is below `2^-22`, less than the gap `1 / d` between
/// `off / d` and the next integer since `d <= 2^20`. The product itself
/// stays below `2^22 * 2^41 < 2^64`.
pub const CLASS_INV: [u64; NUM_CLASSES] = build_inv();

/// Shift matching [`CLASS_INV`].
pub const CLASS_INV_SHIFT: u32 = 44;

const fn build_inv() -> [u64; NUM_CLASSES] {
    let mut t = [0u64; NUM_CLASSES];
    let mut i = 0;
    while i < NUM_CLASSES {
        t[i] = (1u64 << CLASS_INV_SHIFT) / CLASS_SIZE[i] as u64 + 1;
        i += 1;
    }
    t
}

const fn build_table() -> [u32; NUM_CLASSES] {
    let mut t = [0u32; NUM_CLASSES];
    let mut c = 0;
    while c < 8 {
        t[c] = 16 * (c as u32 + 1);
        c += 1;
    }
    while c < NUM_CLASSES {
        let b = 7 + (c - 8) / 4;
        let sub = (c - 8) % 4;
        t[c] = (1 << b) + (sub as u32 + 1) * (1 << (b - 2));
        c += 1;
    }
    t
}

/// The smallest class whose blocks hold `size` bytes. `size` must be at
/// most [`MAX_SMALL`].
#[inline]
pub fn class_for(size: usize) -> usize {
    debug_assert!(size <= MAX_SMALL);
    if size <= 128 {
        return size.saturating_sub(1) / 16;
    }
    let n = size - 1;
    let b = (usize::BITS - 1 - n.leading_zeros()) as usize;
    let sub = (n >> (b - 2)) & 3;
    8 + (b - 7) * 4 + sub
}

/// Size class for a block of `size` bytes aligned to `align` (a power of
/// two no larger than a page). Returns `None` if the request is too big.
#[inline]
pub fn class_for_aligned(size: usize, align: usize) -> Option<usize> {
    let rounded = size.max(1).checked_next_multiple_of(align)?;
    if rounded > MAX_SMALL {
        return None;
    }
    let class = class_for(rounded);
    debug_assert_eq!(CLASS_SIZE[class] as usize % align, 0);
    Some(class)
}

/// Number of 256 KiB units a span of this class occupies: enough for a
/// couple of blocks of the largest classes, at most 8 (2 MiB).
#[inline]
pub fn units_for_class(class: usize) -> usize {
    match CLASS_SIZE[class] {
        0..=32_768 => 1,
        32_769..=131_072 => 4,
        _ => 8,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_is_monotonic_and_bounded() {
        assert_eq!(CLASS_SIZE[0], 16);
        assert_eq!(CLASS_SIZE[7], 128);
        assert_eq!(CLASS_SIZE[8], 160);
        assert_eq!(CLASS_SIZE[11], 256);
        assert_eq!(CLASS_SIZE[12], 320);
        assert_eq!(CLASS_SIZE[NUM_CLASSES - 1] as usize, MAX_SMALL);
        for w in CLASS_SIZE.windows(2) {
            assert!(w[0] < w[1]);
            assert_eq!(w[1] % 16, 0);
        }
    }

    #[test]
    fn class_for_round_trips() {
        for size in 0..=MAX_SMALL {
            let c = class_for(size);
            assert!(CLASS_SIZE[c] as usize >= size, "size {size} class {c}");
            if c > 0 {
                assert!((CLASS_SIZE[c - 1] as usize) < size, "size {size} class {c}");
            }
        }
    }

    #[test]
    fn aligned_classes_are_multiples_of_alignment() {
        for align_shift in 4..=12 {
            let align = 1usize << align_shift;
            for size in (0..=MAX_SMALL).step_by(37) {
                if let Some(c) = class_for_aligned(size, align) {
                    assert!(CLASS_SIZE[c] as usize >= size);
                    assert_eq!(
                        CLASS_SIZE[c] as usize % align,
                        0,
                        "size {size} align {align}"
                    );
                }
            }
        }
        assert!(class_for_aligned(MAX_SMALL, 4096).is_some());
        assert!(class_for_aligned(MAX_SMALL + 1, 16).is_none());
    }
}
