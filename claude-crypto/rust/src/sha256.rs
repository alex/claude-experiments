//! SHA-256 (FIPS 180-4).

use crate::asm;

const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Compress whole 64-byte blocks into `state`.
#[inline]
fn compress(state: &mut [u32; 8], blocks: &[u8]) {
    debug_assert!(blocks.len() % 64 == 0);
    let n = blocks.len() / 64;
    if n == 0 {
        return;
    }
    // SAFETY (all calls below): `state` is a valid, exclusively borrowed
    // 32-byte buffer and `blocks` is valid for reads of `64 * n` bytes; they
    // cannot overlap since one is borrowed mutably.  These are exactly the
    // preconditions of the verified contracts; the required CPU features are
    // checked at run time.
    #[cfg(target_arch = "x86_64")]
    {
        if crate::cpu::has_sha_ni() {
            unsafe { asm::cc_sha256_blocks_x86_shani(state.as_mut_ptr(), blocks.as_ptr(), n) };
            return;
        }
        match crate::cpu::x86_level() {
            crate::cpu::X86Level::Avx2 => unsafe {
                asm::cc_sha256_blocks_x86_avx2(state.as_mut_ptr(), blocks.as_ptr(), n)
            },
            crate::cpu::X86Level::Bmi2 => unsafe {
                asm::cc_sha256_blocks_x86_scalar(state.as_mut_ptr(), blocks.as_ptr(), n)
            },
            crate::cpu::X86Level::Baseline => crate::portable::compress(state, blocks),
        }
    }
    #[cfg(all(target_arch = "aarch64", target_endian = "little"))]
    unsafe {
        asm::cc_sha256_blocks_arm(state.as_mut_ptr(), blocks.as_ptr(), n)
    }
    #[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
    unsafe {
        asm::cc_sha256_blocks_ppc64le(state.as_mut_ptr(), blocks.as_ptr(), n)
    }
}

/// Incremental SHA-256 hasher.
#[derive(Clone)]
pub struct Sha256 {
    state: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total_len: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    /// A fresh hasher.
    pub const fn new() -> Self {
        Sha256 { state: H0, buf: [0; 64], buf_len: 0, total_len: 0 }
    }

    /// Absorb `data`.
    pub fn update(&mut self, mut data: &[u8]) {
        self.total_len = self.total_len.wrapping_add(data.len() as u64);
        if self.buf_len > 0 {
            let take = core::cmp::min(64 - self.buf_len, data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len < 64 {
                return;
            }
            let buf = self.buf;
            compress(&mut self.state, &buf);
            self.buf_len = 0;
        }
        let whole = data.len() & !63;
        compress(&mut self.state, &data[..whole]);
        let rest = &data[whole..];
        self.buf[..rest.len()].copy_from_slice(rest);
        self.buf_len = rest.len();
    }

    /// Finish and return the digest.
    pub fn finalize(mut self) -> [u8; 32] {
        let bits = self.total_len.wrapping_mul(8);
        let mut tail = [0u8; 128];
        tail[..self.buf_len].copy_from_slice(&self.buf[..self.buf_len]);
        tail[self.buf_len] = 0x80;
        let len = if self.buf_len < 56 { 64 } else { 128 };
        tail[len - 8..len].copy_from_slice(&bits.to_be_bytes());
        compress(&mut self.state, &tail[..len]);
        let mut out = [0u8; 32];
        for (i, w) in self.state.iter().enumerate() {
            out[4 * i..4 * i + 4].copy_from_slice(&w.to_be_bytes());
        }
        out
    }
}

/// SHA-256 of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize()
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    extern crate std;

    use super::*;
    use crate::cpu::{has_sha_ni, x86_level, X86Level};

    /// Runs `cc_sha256_blocks_x86_shani` once; used by `sha_ni_executes` in a
    /// child process (which dies of SIGILL if the CPU lacks SHA-NI).
    #[test]
    #[ignore = "helper, run in a child process by `implementations_agree`"]
    fn sha_ni_probe() {
        let mut s = H0;
        let block = [0u8; 64];
        unsafe { asm::cc_sha256_blocks_x86_shani(s.as_mut_ptr(), block.as_ptr(), 1) };
    }

    /// Whether the SHA-NI code can be tested here: CPUID reports SHA-NI, or
    /// the CPU executes the instructions anyway (some CPUs/VMs do not
    /// advertise them), as checked by running `sha_ni_probe` in a child process.
    fn sha_ni_executes() -> bool {
        if has_sha_ni() {
            return true;
        }
        let Ok(exe) = std::env::current_exe() else { return false };
        std::process::Command::new(exe)
            .args(["--exact", "sha256::tests::sha_ni_probe", "--ignored", "--test-threads=1"])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .map_or(false, |st| st.success())
    }

    /// The SHA-NI code against the portable reference, from random hash
    /// values and for 0 to 40 blocks.
    #[test]
    fn sha_ni_random() {
        if !sha_ni_executes() {
            std::eprintln!("note: SHA-NI not available, cc_sha256_blocks_x86_shani not tested");
            return;
        }
        let mut x: u64 = 0x0123_4567_89ab_cdef;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let mut data = [0u8; 64 * 40];
        for iter in 0..400 {
            let n = iter % 41;
            for b in data.iter_mut() {
                *b = next() as u8;
            }
            let mut h = [0u32; 8];
            for w in h.iter_mut() {
                *w = next() as u32;
            }
            let blocks = &data[..64 * n];
            let mut reference = h;
            crate::portable::compress(&mut reference, blocks);
            let mut s = h;
            unsafe { asm::cc_sha256_blocks_x86_shani(s.as_mut_ptr(), blocks.as_ptr(), n) };
            assert_eq!(s, reference, "sha-ni, {n} blocks");
        }
    }

    /// All implementations available on this CPU agree (the dispatcher only
    /// ever picks one of them).
    #[test]
    fn implementations_agree() {
        let level = x86_level();
        let sha_ni = sha_ni_executes();
        if !sha_ni {
            std::eprintln!("note: SHA-NI not available, cc_sha256_blocks_x86_shani not tested");
        }
        let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut data = [0u8; 64 * 9];
        for n in 0..=9 {
            for b in data.iter_mut() {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                *b = x as u8;
            }
            let blocks = &data[..64 * n];
            let mut reference = H0;
            crate::portable::compress(&mut reference, blocks);
            if level != X86Level::Baseline {
                let mut s = H0;
                unsafe { asm::cc_sha256_blocks_x86_scalar(s.as_mut_ptr(), blocks.as_ptr(), n) };
                assert_eq!(s, reference, "scalar, {n} blocks");
            }
            if level == X86Level::Avx2 {
                let mut s = H0;
                unsafe { asm::cc_sha256_blocks_x86_avx2(s.as_mut_ptr(), blocks.as_ptr(), n) };
                assert_eq!(s, reference, "avx2, {n} blocks");
            }
            if sha_ni {
                let mut s = H0;
                unsafe { asm::cc_sha256_blocks_x86_shani(s.as_mut_ptr(), blocks.as_ptr(), n) };
                assert_eq!(s, reference, "sha-ni, {n} blocks");
            }
        }
    }
}
