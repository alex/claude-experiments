//! Static thread-local storage.
//!
//! A statically linked executable has at most one TLS segment (`PT_TLS`).
//! We use the "variant II" layout mandated for x86_64: the TLS block is
//! placed directly below the thread pointer, and the thread pointer itself
//! addresses the [`Tcb`]. Compiled code accesses a variable at
//! `%fs:-(round_up(memsz, align) - offset)`, so the block must start
//! exactly `round_up(memsz, align)` bytes below the TCB.
//!
//! ```text
//!  region (aligned to A)                                  tp = TCB
//!  |  slack  |  TLS image (filesz) | zeroes (memsz-filesz) |  Tcb  |
//!             ^ block = tp - round_up(memsz, align)
//! ```

use super::Tcb;
use core::cell::UnsafeCell;

/// ELF64 program header.
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Elf64Phdr {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: u64,
    pub p_vaddr: u64,
    pub p_paddr: u64,
    pub p_filesz: u64,
    pub p_memsz: u64,
    pub p_align: u64,
}

/// `p_type` of the TLS segment.
pub const PT_TLS: u32 = 7;

/// Description of the executable's TLS initialisation image.
#[derive(Clone, Copy, Debug)]
pub struct Image {
    /// Start of the initialised data in the executable image.
    pub addr: *const u8,
    /// Bytes to copy from `addr`.
    pub filesz: usize,
    /// Total size of the block (the tail is zero-initialised).
    pub memsz: usize,
    /// Required alignment of the block.
    pub align: usize,
}

impl Image {
    const EMPTY: Image = Image {
        addr: core::ptr::null(),
        filesz: 0,
        memsz: 0,
        align: 1,
    };

    /// Size of the TLS block as seen by the linker (variant I adds the
    /// header, rounded to the block's alignment).
    fn block_size(&self) -> usize {
        round_up(self.memsz, self.align) + round_up(TP_HEADER, self.align)
    }

    /// Alignment of the whole region (TLS block plus TCB).
    fn region_align(&self) -> usize {
        self.align.max(core::mem::align_of::<Tcb>()).max(64)
    }

    /// Number of bytes a caller must provide to [`install`].
    pub fn region_size(&self) -> usize {
        // One `region_align` of slack to align the start, another so the
        // TCB (variant II) or the thread pointer (variant I) can be
        // rounded up to `region_align` as well, plus the variant I
        // header.
        2 * self.region_align() + self.block_size() + core::mem::size_of::<Tcb>() + TP_HEADER
    }
}

struct ImageCell(UnsafeCell<Image>);
// SAFETY: written once during single-threaded startup, read-only after.
unsafe impl Sync for ImageCell {}

static IMAGE: ImageCell = ImageCell(UnsafeCell::new(Image::EMPTY));

/// Records the TLS segment from the program headers. Must be called once,
/// before any thread is created.
///
/// # Safety
/// `phdr` must point to `phnum` valid program headers.
pub unsafe fn init_from_phdrs(phdr: *const Elf64Phdr, phnum: usize) {
    for i in 0..phnum {
        // SAFETY: within the header table.
        let ph = unsafe { *phdr.add(i) };
        if ph.p_type == PT_TLS {
            let image = Image {
                addr: ph.p_vaddr as usize as *const u8,
                filesz: ph.p_filesz as usize,
                memsz: ph.p_memsz as usize,
                align: (ph.p_align as usize).max(1),
            };
            // SAFETY: startup is single-threaded.
            unsafe { *IMAGE.0.get() = image };
            return;
        }
    }
}

/// The recorded TLS image.
pub fn image() -> Image {
    // SAFETY: only mutated during single-threaded startup.
    unsafe { *IMAGE.0.get() }
}

/// Bytes required for a thread's TLS block and TCB.
pub fn region_size() -> usize {
    image().region_size()
}

/// Size of the header at the thread pointer in the variant I layout
/// (two words, conventionally the DTV pointer and a reserved word).
#[cfg(target_arch = "x86_64")]
const TP_HEADER: usize = 0;
#[cfg(not(target_arch = "x86_64"))]
const TP_HEADER: usize = 16;

/// The thread pointer register value for a TCB: the TCB itself in the
/// variant II layout, the header right after it in variant I.
#[inline(always)]
pub fn thread_pointer_of(tcb: *mut Tcb) -> *mut u8 {
    #[cfg(target_arch = "x86_64")]
    {
        tcb as *mut u8
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        (tcb as usize + core::mem::size_of::<Tcb>()) as *mut u8
    }
}

/// The TCB behind a thread pointer register value (the inverse of
/// [`thread_pointer_of`]).
#[inline(always)]
pub fn tcb_of(tp: *mut u8) -> *mut Tcb {
    #[cfg(target_arch = "x86_64")]
    {
        tp as *mut Tcb
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        (tp as usize - core::mem::size_of::<Tcb>()) as *mut Tcb
    }
}

/// Lays out a TLS block and TCB inside `region`, which must hold at least
/// [`region_size`] bytes, and returns the TCB (see [`thread_pointer_of`]
/// for the register value).
///
/// # Safety
/// `region` must be valid for writes of `len` bytes and unused.
#[cfg(target_arch = "x86_64")]
pub unsafe fn install(region: *mut u8, len: usize, canary: usize) -> *mut Tcb {
    let image = image();
    assert!(len >= image.region_size(), "TLS region too small");
    let align = image.region_align();
    let base = round_up(region as usize, align);
    let tp = round_up(base + image.block_size(), align);
    let block = (tp - image.block_size()) as *mut u8;
    // SAFETY: `block..tp` lies inside `region` by construction, and the
    // image is part of the executable so it is readable.
    unsafe {
        core::ptr::copy_nonoverlapping(image.addr, block, image.filesz);
        core::ptr::write_bytes(block.add(image.filesz), 0, image.memsz - image.filesz);
        let tcb = tp as *mut Tcb;
        Tcb::init(tcb, canary);
        tcb
    }
}

/// Variant I (AArch64): the thread pointer addresses a 16-byte header
/// and the TLS block follows it at `round_up(16, align)`; compiled code
/// reads a variable at `tp + round_up(16, align) + offset`. Our TCB sits
/// immediately below the thread pointer.
///
/// ```text
///  region (aligned to A)
///  |  slack  |  Tcb  | header | TLS image (filesz) | zeroes (memsz-filesz) |
///                    ^ tp     ^ block = tp + round_up(16, align)
/// ```
///
/// # Safety
/// `region` must be valid for writes of `len` bytes and unused.
#[cfg(not(target_arch = "x86_64"))]
pub unsafe fn install(region: *mut u8, len: usize, canary: usize) -> *mut Tcb {
    let image = image();
    assert!(len >= image.region_size(), "TLS region too small");
    let align = image.region_align();
    let base = round_up(region as usize, align);
    let tp = round_up(base + core::mem::size_of::<Tcb>(), align);
    let tcb = tcb_of(tp as *mut u8);
    let block = (tp + round_up(TP_HEADER, image.align)) as *mut u8;
    // SAFETY: everything lies inside `region` by construction, and the
    // image is part of the executable so it is readable.
    unsafe {
        core::ptr::write_bytes(tp as *mut u8, 0, TP_HEADER);
        core::ptr::copy_nonoverlapping(image.addr, block, image.filesz);
        core::ptr::write_bytes(block.add(image.filesz), 0, image.memsz - image.filesz);
        Tcb::init(tcb, canary);
        tcb
    }
}

/// Rounds `v` up to a multiple of `align` (a power of two).
pub const fn round_up(v: usize, align: usize) -> usize {
    (v + align - 1) & !(align - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_matches_linker_expectations() {
        let data = [1u8, 2, 3, 4, 5];
        let image = Image {
            addr: data.as_ptr(),
            filesz: 5,
            memsz: 12,
            align: 8,
        };
        // SAFETY: test-only mutation before any use.
        unsafe { *IMAGE.0.get() = image };
        let mut region = vec![0xAAu8; region_size() + 100];
        // SAFETY: the buffer is large enough.
        let tcb = unsafe { install(region.as_mut_ptr().add(3), region.len() - 3, 0x1234_5600) };
        let tp = tcb as usize;
        assert_eq!(tp % 64, 0);
        let block = (tp - 16) as *const u8;
        // SAFETY: inside the region.
        let bytes = unsafe { core::slice::from_raw_parts(block, 16) };
        assert_eq!(&bytes[..5], &[1, 2, 3, 4, 5]);
        assert!(bytes[5..12].iter().all(|&b| b == 0));
        // SAFETY: the TCB was initialised by install.
        unsafe {
            assert_eq!((*tcb).self_ptr, tcb);
            assert_eq!((*tcb).stack_guard, 0x1234_5600);
        }
        // SAFETY: restore.
        unsafe { *IMAGE.0.get() = Image::EMPTY };
    }

    #[test]
    fn round_up_works() {
        assert_eq!(round_up(0, 8), 0);
        assert_eq!(round_up(1, 8), 8);
        assert_eq!(round_up(8, 8), 8);
        assert_eq!(round_up(9, 64), 64);
    }
}
