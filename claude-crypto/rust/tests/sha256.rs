use claude_crypto::{sha256, Sha256};
use sha2::Digest;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn known_answers() {
    assert_eq!(hex(&sha256(b"")), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(hex(&sha256(b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert_eq!(
        hex(&sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
    let million_a = vec![b'a'; 1_000_000];
    assert_eq!(hex(&sha256(&million_a)), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

#[test]
fn matches_reference_random() {
    let mut x: u64 = 0x1234_5678_9abc_def0;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for i in 0..3000 {
        let len = (next() % if i < 500 { 200 } else { 5000 }) as usize;
        let data: Vec<u8> = (0..len).map(|_| next() as u8).collect();
        assert_eq!(sha256(&data), <[u8; 32]>::from(sha2::Sha256::digest(&data)), "len {len}");
        // incremental, in random-sized pieces
        let mut h = Sha256::new();
        let mut rest = &data[..];
        while !rest.is_empty() {
            let k = (next() as usize % 100).min(rest.len());
            h.update(&rest[..k]);
            rest = &rest[k..];
        }
        assert_eq!(h.finalize(), sha256(&data));
    }
}
