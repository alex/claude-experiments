//! The `str*` family.

use crate::c_char;
use core::arch::x86_64::{__m128i, _mm_cmpeq_epi8, _mm_load_si128, _mm_movemask_epi8, _mm_setzero_si128};

/// Length of the NUL-terminated string at `s`.
///
/// Reads 16 bytes at a time from 16-byte aligned addresses. Such a read
/// never crosses a page boundary, so it cannot fault as long as the string
/// itself (including its terminator) is readable.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline]
pub unsafe fn strlen_impl(s: *const u8) -> usize {
    // SAFETY: see the function documentation for why the over-read is fine.
    unsafe {
        let start = s as usize;
        let mut p = (start & !15) as *const __m128i;
        let zero = _mm_setzero_si128();
        let mut mask = _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_load_si128(p), zero)) as u32;
        // Ignore bytes before the start of the string.
        mask >>= start & 15;
        if mask != 0 {
            return mask.trailing_zeros() as usize;
        }
        loop {
            p = p.add(1);
            let mask = _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_load_si128(p), zero)) as u32;
            if mask != 0 {
                return (p as usize - start) + mask.trailing_zeros() as usize;
            }
        }
    }
}

/// `strlen(3)`.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strlen(s: *const c_char) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe { strlen_impl(s as *const u8) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strlen_various_offsets() {
        // A 64-byte aligned buffer so we can test every alignment.
        #[repr(align(64))]
        struct Buf([u8; 256]);
        let mut buf = Buf([b'x'; 256]);
        for len in 0..100 {
            for off in 0..40 {
                buf.0.fill(b'x');
                buf.0[off + len] = 0;
                // SAFETY: NUL terminated within the buffer.
                assert_eq!(unsafe { strlen_impl(buf.0.as_ptr().add(off)) }, len, "len={len} off={off}");
            }
        }
    }
}
