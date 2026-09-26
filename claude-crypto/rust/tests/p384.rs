use claude_crypto::p384;

fn unhex<const N: usize>(s: &str) -> [u8; N] {
    assert_eq!(s.len(), 2 * N);
    let mut out = [0u8; N];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
    }
    out
}

/// The OpenSSL-generated vectors of `test/p384_vectors.txt` (see `test/p384_gen.c`):
/// random valid and mutated signatures, e ≥ n, e = 0, r/s edge values, public keys
/// G and −G, crafted scalars hitting the doubling cases and R = O, invalid keys.
#[test]
fn vectors() {
    let v = match p384::Verifier::new() {
        Ok(v) => v,
        Err(e) => {
            eprintln!("skipping: {e}");
            return;
        }
    };
    let text = include_str!("../../test/p384_vectors.txt");
    let (mut n, mut valid) = (0, 0);
    for line in text.lines().filter(|l| !l.is_empty()) {
        let f: Vec<&str> = line.split(' ').collect();
        let (pk, dg, sg) = (unhex::<96>(f[0]), unhex::<48>(f[1]), unhex::<96>(f[2]));
        let expect = f[3] == "1";
        assert_eq!(v.verify(&pk, &dg, &sg), expect, "vector {}", n + 1);
        assert_eq!(p384::verify(&pk, &dg, &sg), Ok(expect));
        n += 1;
        valid += expect as usize;
    }
    assert!(n > 700 && valid > 100, "{n} vectors, {valid} valid");
}

#[cfg(target_arch = "x86_64")]
#[test]
fn matches_openssl_random() {
    use openssl::bn::BigNumContext;
    use openssl::ec::{EcGroup, EcKey, PointConversionForm};
    use openssl::ecdsa::EcdsaSig;
    use openssl::nid::Nid;

    let Ok(v) = p384::Verifier::new() else { return };
    let group = EcGroup::from_curve_name(Nid::SECP384R1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let mut x: u64 = 0x0123_4567_89ab_cdef;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for i in 0..40 {
        let key = EcKey::generate(&group).unwrap();
        let pt = key.public_key().to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx).unwrap();
        let pk: [u8; 96] = pt[1..].try_into().unwrap();
        let mut dg = [0u8; 48];
        dg.iter_mut().for_each(|b| *b = next() as u8);
        let sig = EcdsaSig::sign(&dg, &key).unwrap();
        let mut sg = [0u8; 96];
        sg[..48].copy_from_slice(&sig.r().to_vec_padded(48).unwrap());
        sg[48..].copy_from_slice(&sig.s().to_vec_padded(48).unwrap());
        assert!(v.verify(&pk, &dg, &sg));
        // one-bit mutations of the digest and the signature are rejected by both
        let mut dg2 = dg;
        dg2[i % 48] ^= 1 << (i % 8);
        let mut sg2 = sg;
        sg2[(i * 7) % 96] ^= 1 << (i % 8);
        for (d, s) in [(&dg2, &sg), (&dg, &sg2)] {
            let osig = EcdsaSig::from_private_components(
                openssl::bn::BigNum::from_slice(&s[..48]).unwrap(),
                openssl::bn::BigNum::from_slice(&s[48..]).unwrap(),
            )
            .unwrap();
            let theirs = osig.verify(d, &key).unwrap_or(false);
            assert_eq!(v.verify(&pk, d, s), theirs);
        }
    }
}
