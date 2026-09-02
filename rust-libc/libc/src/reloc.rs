//! Self-relocation of a static PIE.
//!
//! A `-static-pie` executable is loaded at a random address and carries
//! `R_*_RELATIVE` relocations for every absolute pointer in its data
//! (function tables, string tables, the GOT, `.init_array`, ...). With no
//! dynamic linker to apply them, the executable must do it itself, before
//! it touches any of that data. [`relocate`] therefore runs first thing in
//! `start_c` and is written to use nothing but its stack, PC-relative
//! addresses and the program headers: no statics, no panics, no bounds
//! checks that could panic.
//!
//! A non-PIE static executable has no `PT_DYNAMIC` and is left alone.

use crate::thread::tls::Elf64Phdr;

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_GNU_RELRO: u32 = 0x6474_e552;
const DT_NULL: i64 = 0;
const DT_RELA: i64 = 7;
const DT_RELASZ: i64 = 8;
const DT_RELRSZ: i64 = 35;
const DT_RELR: i64 = 36;

#[repr(C)]
struct Dyn {
    tag: i64,
    val: u64,
}

#[repr(C)]
struct Rela {
    offset: u64,
    info: u64,
    addend: i64,
}

/// Applies the executable's relative relocations, write-protects its
/// RELRO segment and returns its load bias (the difference between
/// runtime and link-time addresses; zero for a non-PIE executable).
///
/// Inlined into its caller because, on x86_64, Rust calls functions
/// through the GOT, whose entries are exactly what has not been
/// relocated yet.
///
/// # Safety
/// Must be called exactly once, before anything else in the process
/// reads a relocated pointer.
#[inline(always)]
pub unsafe fn relocate() -> usize {
    let ehdr = crate::arch::ehdr_start();
    // SAFETY: the ELF header is mapped (the linker put it in the first
    // segment); the program headers follow at `e_phoff`.
    unsafe {
        let phoff = (ehdr.add(32) as *const u64).read_unaligned() as usize;
        let phnum = (ehdr.add(56) as *const u16).read_unaligned() as usize;
        let phdr = ehdr.add(phoff) as *const Elf64Phdr;
        let mut bias = 0usize;
        let mut dynamic = 0usize;
        let mut relro: Option<(usize, usize)> = None;
        let mut i = 0;
        while i < phnum {
            let ph = &*phdr.add(i);
            i += 1;
            match ph.p_type {
                // The segment holding the ELF header: its link-time
                // address against the header's runtime address gives
                // the bias.
                PT_LOAD if ph.p_offset == 0 => {
                    bias = (ehdr as usize).wrapping_sub(ph.p_vaddr as usize);
                }
                PT_DYNAMIC => dynamic = ph.p_vaddr as usize,
                PT_GNU_RELRO => relro = Some((ph.p_vaddr as usize, ph.p_memsz as usize)),
                _ => {}
            }
        }
        // A fixed-address executable has no dynamic section and nothing to
        // relocate (but still gets its RELRO segment protected below).
        if dynamic == 0 {
            bias = 0;
        }
        let (mut rela, mut relasz, mut relr, mut relrsz) = (0usize, 0usize, 0usize, 0usize);
        if dynamic != 0 {
            let mut dynv = bias.wrapping_add(dynamic) as *const Dyn;
            while (*dynv).tag != DT_NULL {
                match (*dynv).tag {
                    DT_RELA => rela = (*dynv).val as usize,
                    DT_RELASZ => relasz = (*dynv).val as usize,
                    DT_RELR => relr = (*dynv).val as usize,
                    DT_RELRSZ => relrsz = (*dynv).val as usize,
                    _ => {}
                }
                dynv = dynv.add(1);
            }
        }
        if rela != 0 {
            let mut r = bias.wrapping_add(rela) as *const Rela;
            let end = (r as *const u8).add(relasz) as *const Rela;
            while r < end {
                // Only relative relocations exist in a static PIE (every
                // symbol was resolved at link time); anything else is
                // left untouched.
                if (*r).info as u32 == crate::arch::R_RELATIVE {
                    let at = bias.wrapping_add((*r).offset as usize) as *mut usize;
                    *at = bias.wrapping_add((*r).addend as usize);
                }
                r = r.add(1);
            }
        }
        if relr != 0 {
            // RELR packs relative relocations: an even word is an address
            // to relocate, an odd word a bitmap of the following 63 words
            // to relocate (bit 0 corresponds to the word after the last
            // address).
            let mut w = bias.wrapping_add(relr) as *const usize;
            let end = (w as *const u8).add(relrsz) as *const usize;
            let mut at = core::ptr::null_mut::<usize>();
            while w < end {
                let entry = *w;
                w = w.add(1);
                if entry & 1 == 0 {
                    at = bias.wrapping_add(entry) as *mut usize;
                    *at = (*at).wrapping_add(bias);
                    at = at.add(1);
                } else {
                    let mut bits = entry >> 1;
                    let mut k = 0;
                    while bits != 0 {
                        if bits & 1 != 0 {
                            let p = at.add(k);
                            *p = (*p).wrapping_add(bias);
                        }
                        bits >>= 1;
                        k += 1;
                    }
                    at = at.add(63);
                }
            }
        }
        // The read-only-after-relocation data (RELRO: `.init_array`, the
        // GOT, `const` tables of pointers, ...) is now final: take the
        // write permission away, as the dynamic linker would.
        if let Some((vaddr, len)) = relro {
            let start = bias.wrapping_add(vaddr) & !(crate::sys::PAGE_SIZE - 1);
            let end = bias.wrapping_add(vaddr).wrapping_add(len);
            if end > start {
                let _ = crate::sys::mprotect(start as *mut u8, end - start, crate::sys::PROT_READ);
            }
        }
        bias
    }
}
