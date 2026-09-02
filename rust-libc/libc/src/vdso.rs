//! The vDSO: kernel-provided user-space implementations of the clock
//! calls, found through `AT_SYSINFO_EHDR` at startup.
//!
//! The vDSO is an ELF shared object mapped by the kernel. Its dynamic
//! section gives the symbol and string tables; the symbol count comes from
//! the `DT_HASH` table (or `DT_GNU_HASH` when that is all there is). Only
//! defined function symbols are accepted, and every offset is checked
//! against the mapping's extent before it is dereferenced, so a
//! malformed object cannot make startup read outside it.

use crate::start::{auxv, auxval};
use crate::sys::Timespec;
use core::ffi::c_int;
use core::sync::atomic::{AtomicUsize, Ordering};

/// `int (*)(clockid_t, struct timespec *)`.
type ClockGettime = unsafe extern "C" fn(c_int, *mut Timespec) -> c_int;
/// `int (*)(unsigned *cpu, unsigned *node, void *cache)`.
type Getcpu = unsafe extern "C" fn(*mut u32, *mut u32, *mut u8) -> c_int;

static CLOCK_GETTIME: AtomicUsize = AtomicUsize::new(0);
static GETCPU: AtomicUsize = AtomicUsize::new(0);

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const DT_HASH: i64 = 4;
const DT_STRTAB: i64 = 5;
const DT_SYMTAB: i64 = 6;
const DT_GNU_HASH: i64 = 0x6fff_fef5;
const STT_FUNC: u8 = 2;

/// A mapped ELF image with bounds-checked accessors.
struct Image {
    /// Address of the ELF header.
    base: usize,
    /// Bytes mapped from `base`.
    len: usize,
    /// Runtime address minus link-time address.
    bias: usize,
}

impl Image {
    /// Reads a `T` at runtime address `addr` if it lies inside the image.
    fn read<T: Copy>(&self, addr: usize) -> Option<T> {
        let off = addr.checked_sub(self.base)?;
        if off.checked_add(core::mem::size_of::<T>())? > self.len
            || !addr.is_multiple_of(core::mem::align_of::<T>())
        {
            return None;
        }
        // SAFETY: the address is inside the kernel-provided mapping and
        // aligned; every `T` used here is plain data.
        Some(unsafe { core::ptr::read(addr as *const T) })
    }

    /// The NUL-terminated string at `addr`, if it ends inside the image.
    fn cstr(&self, addr: usize) -> Option<&[u8]> {
        let off = addr.checked_sub(self.base)?;
        let end = self.len.checked_sub(off)?;
        // SAFETY: the range is inside the mapping.
        let bytes = unsafe { core::slice::from_raw_parts(addr as *const u8, end) };
        let n = bytes.iter().position(|&b| b == 0)?;
        Some(&bytes[..n])
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Phdr {
    p_type: u32,
    p_flags: u32,
    p_offset: u64,
    p_vaddr: u64,
    p_paddr: u64,
    p_filesz: u64,
    p_memsz: u64,
    p_align: u64,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Dyn {
    d_tag: i64,
    d_val: u64,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Sym {
    st_name: u32,
    st_info: u8,
    st_other: u8,
    st_shndx: u16,
    st_value: u64,
    st_size: u64,
}

/// Locates the vDSO and records the entry points it provides. Called
/// once during startup; without a vDSO every clock call stays a system
/// call.
pub fn init() {
    let Some(base) = auxval(auxv::AT_SYSINFO_EHDR).filter(|&b| b != 0) else {
        return;
    };
    let mut img = Image {
        base,
        // Enough for the headers; refined from the load segment below.
        len: 64,
        bias: 0,
    };
    // e_phoff at 32, e_phentsize at 54, e_phnum at 56.
    let (Some(phoff), Some(phentsize), Some(phnum)) = (
        img.read::<u64>(base + 32),
        img.read::<u16>(base + 54),
        img.read::<u16>(base + 56),
    ) else {
        return;
    };
    if phentsize as usize != core::mem::size_of::<Phdr>() {
        return;
    }
    // The program headers must be mapped along with the header page.
    img.len = crate::sys::PAGE_SIZE.max(phoff as usize + phnum as usize * phentsize as usize);
    let mut dynamic = None;
    let mut load: Option<Phdr> = None;
    for i in 0..phnum as usize {
        let Some(ph) = img.read::<Phdr>(base + phoff as usize + i * phentsize as usize) else {
            return;
        };
        match ph.p_type {
            PT_LOAD if load.is_none() => load = Some(ph),
            PT_DYNAMIC => dynamic = Some(ph),
            _ => {}
        }
    }
    let (Some(load), Some(dynamic)) = (load, dynamic) else {
        return;
    };
    // The image starts at the first load segment (offset 0 in the file).
    if load.p_offset != 0 {
        return;
    }
    img.bias = base.wrapping_sub(load.p_vaddr as usize);
    img.len = load.p_memsz as usize;
    let (mut symtab, mut strtab, mut hash, mut gnu_hash) = (0usize, 0usize, 0usize, 0usize);
    let mut d = img.bias.wrapping_add(dynamic.p_vaddr as usize);
    loop {
        let Some(entry) = img.read::<Dyn>(d) else {
            return;
        };
        match entry.d_tag {
            0 => break,
            DT_SYMTAB => symtab = img.bias.wrapping_add(entry.d_val as usize),
            DT_STRTAB => strtab = img.bias.wrapping_add(entry.d_val as usize),
            DT_HASH => hash = img.bias.wrapping_add(entry.d_val as usize),
            DT_GNU_HASH => gnu_hash = img.bias.wrapping_add(entry.d_val as usize),
            _ => {}
        }
        d += core::mem::size_of::<Dyn>();
    }
    if symtab == 0 || strtab == 0 {
        return;
    }
    let Some(count) = symbol_count(&img, hash, gnu_hash) else {
        return;
    };
    for i in 0..count {
        let Some(sym) = img.read::<Sym>(symtab + i * core::mem::size_of::<Sym>()) else {
            return;
        };
        if sym.st_shndx == 0 || sym.st_info & 0xf != STT_FUNC {
            continue;
        }
        let Some(name) = img.cstr(strtab + sym.st_name as usize) else {
            continue;
        };
        let addr = img.bias.wrapping_add(sym.st_value as usize);
        if addr < img.base || addr >= img.base + img.len {
            continue;
        }
        if name == crate::arch::VDSO_CLOCK_GETTIME {
            CLOCK_GETTIME.store(addr, Ordering::Relaxed);
        } else if name == crate::arch::VDSO_GETCPU {
            GETCPU.store(addr, Ordering::Relaxed);
        }
    }
}

/// Number of entries in the dynamic symbol table.
fn symbol_count(img: &Image, hash: usize, gnu_hash: usize) -> Option<usize> {
    if hash != 0 {
        // SysV hash: nbucket, nchain; nchain equals the symbol count.
        return img.read::<u32>(hash + 4).map(|n| n as usize);
    }
    if gnu_hash == 0 {
        return None;
    }
    // GNU hash: nbuckets, symoffset, bloom_size, bloom_shift, bloom[],
    // buckets[], chains[]. The last symbol is the end of the longest
    // chain starting from the highest bucket.
    let nbuckets = img.read::<u32>(gnu_hash)? as usize;
    let symoffset = img.read::<u32>(gnu_hash + 4)? as usize;
    let bloom_size = img.read::<u32>(gnu_hash + 8)? as usize;
    let buckets = gnu_hash + 16 + bloom_size * 8;
    let chains = buckets + nbuckets * 4;
    let mut last = 0usize;
    for b in 0..nbuckets {
        let v = img.read::<u32>(buckets + b * 4)? as usize;
        last = last.max(v);
    }
    if last < symoffset {
        return Some(symoffset);
    }
    loop {
        let c = img.read::<u32>(chains + (last - symoffset) * 4)?;
        if c & 1 != 0 {
            return Some(last + 1);
        }
        last += 1;
    }
}

/// `clock_gettime` through the vDSO, or `None` if it has none. A negative
/// return is the kernel's error number.
///
/// # Safety
/// `ts` must be valid.
#[inline]
pub unsafe fn clock_gettime(clock: c_int, ts: *mut Timespec) -> Option<c_int> {
    let f = CLOCK_GETTIME.load(Ordering::Relaxed);
    if f == 0 {
        return None;
    }
    // SAFETY: the address was validated by `init` to be a defined function
    // symbol inside the vDSO; the kernel guarantees its signature.
    let f: ClockGettime = unsafe { core::mem::transmute::<usize, ClockGettime>(f) };
    // SAFETY: `ts` is the caller's valid pointer.
    Some(unsafe { f(clock, ts) })
}

/// `getcpu` through the vDSO, or `None`.
///
/// # Safety
/// `cpu` must be valid.
#[inline]
pub unsafe fn getcpu(cpu: *mut u32) -> Option<c_int> {
    let f = GETCPU.load(Ordering::Relaxed);
    if f == 0 {
        return None;
    }
    // SAFETY: as for `clock_gettime`.
    let f: Getcpu = unsafe { core::mem::transmute::<usize, Getcpu>(f) };
    // SAFETY: `cpu` is valid; node and cache may be null.
    Some(unsafe { f(cpu, core::ptr::null_mut(), core::ptr::null_mut()) })
}
