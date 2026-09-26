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
    // SAFETY: `state` is a valid, exclusively borrowed 32-byte buffer and
    // `blocks` is valid for reads of `64 * n` bytes; they cannot overlap since
    // one is borrowed mutably.  These are exactly the preconditions of the
    // verified contract.
    #[cfg(target_arch = "x86_64")]
    unsafe {
        asm::cc_sha256_blocks_x86_scalar(state.as_mut_ptr(), blocks.as_ptr(), n)
    }
    #[cfg(all(target_arch = "aarch64", target_endian = "little"))]
    unsafe {
        asm::cc_sha256_blocks_arm(state.as_mut_ptr(), blocks.as_ptr(), n)
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
