//! `cargo bench` — compares against OpenSSL (via the `openssl` crate).

use std::time::Instant;

fn time<F: FnMut()>(mut f: F, iters: usize) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..5 {
        let t = Instant::now();
        for _ in 0..iters {
            f();
        }
        best = best.min(t.elapsed().as_secs_f64());
    }
    best
}

fn main() {
    for &size in &[64usize, 1024, 16384] {
        let data = vec![0x5au8; size];
        let iters = 200_000_000 / size.max(1) / 10;
        let ours = time(|| { std::hint::black_box(claude_crypto::sha256(std::hint::black_box(&data))); }, iters);
        #[cfg(target_arch = "x86_64")]
        let ossl = time(|| { std::hint::black_box(openssl::sha::sha256(std::hint::black_box(&data))); }, iters);
        #[cfg(not(target_arch = "x86_64"))]
        let ossl = f64::NAN;
        let mb = |t: f64| (size * iters) as f64 / t / 1e6;
        println!("sha256 {size:>6} bytes: claude-crypto {:8.1} MB/s   openssl {:8.1} MB/s", mb(ours), mb(ossl));
    }
}
