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

    p384_bench();
}

/// ECDSA-P384 verification of one valid signature (from the test vectors).
fn p384_bench() {
    let text = include_str!("../../test/p384_vectors.txt");
    let line = text.lines().find(|l| l.ends_with(" 1")).unwrap();
    let f: Vec<&str> = line.split(' ').collect();
    let unhex = |s: &str| -> Vec<u8> { (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect() };
    let pk: [u8; 96] = unhex(f[0]).try_into().unwrap();
    let dg: [u8; 48] = unhex(f[1]).try_into().unwrap();
    let sg: [u8; 96] = unhex(f[2]).try_into().unwrap();
    let iters = 2000;
    let ours = match claude_crypto::p384::Verifier::new() {
        Ok(v) => time(|| assert!(v.verify(std::hint::black_box(&pk), &dg, &sg)), iters),
        Err(_) => f64::NAN,
    };
    #[cfg(target_arch = "x86_64")]
    let ossl = {
        use openssl::bn::{BigNum, BigNumContext};
        use openssl::ec::{EcGroup, EcKey, EcPoint};
        use openssl::ecdsa::EcdsaSig;
        let group = EcGroup::from_curve_name(openssl::nid::Nid::SECP384R1).unwrap();
        let mut ctx = BigNumContext::new().unwrap();
        let mut pt = vec![4u8];
        pt.extend_from_slice(&pk);
        let point = EcPoint::from_bytes(&group, &pt, &mut ctx).unwrap();
        let key = EcKey::from_public_key(&group, &point).unwrap();
        let sig = EcdsaSig::from_private_components(BigNum::from_slice(&sg[..48]).unwrap(), BigNum::from_slice(&sg[48..]).unwrap()).unwrap();
        time(|| assert!(sig.verify(std::hint::black_box(&dg), &key).unwrap()), iters)
    };
    #[cfg(not(target_arch = "x86_64"))]
    let ossl = f64::NAN;
    println!(
        "p384 verify:        claude-crypto {:8.0} verify/s   openssl {:8.0} verify/s",
        iters as f64 / ours,
        iters as f64 / ossl
    );
}
