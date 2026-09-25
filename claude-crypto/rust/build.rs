//! Assembles the Lean-generated (and Lean-verified) assembly for the target
//! architecture.

use std::path::PathBuf;

fn main() {
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let endian = std::env::var("CARGO_CFG_TARGET_ENDIAN").unwrap();
    let dir = match (arch.as_str(), endian.as_str()) {
        ("x86_64", _) => "x86_64",
        ("aarch64", "little") => "aarch64",
        ("powerpc64", "little") => "ppc64le",
        _ => panic!("claude-crypto: unsupported target {arch} ({endian}-endian)"),
    };
    let asm_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("..")
        .join("asm")
        .join(dir);
    let mut build = cc::Build::new();
    let mut files: Vec<_> = std::fs::read_dir(&asm_dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", asm_dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map_or(false, |e| e == "S"))
        .collect();
    files.sort();
    for f in &files {
        println!("cargo:rerun-if-changed={}", f.display());
        build.file(f);
    }
    println!("cargo:rerun-if-changed={}", asm_dir.display());
    build.compile("claude_crypto_asm");
}
