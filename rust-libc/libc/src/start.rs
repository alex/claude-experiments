//! Process startup: from `_start` to `main`.
//!
//! [`start_c`] receives the initial stack pointer from the assembly entry
//! point, unpacks `argc`/`argv`/`envp`/auxv, sets up the main thread's TLS
//! and TCB, runs the ELF constructors and finally calls `main`.

use crate::c_char;
use crate::thread::tls;
use core::cell::UnsafeCell;
use core::ffi::c_int;

/// The C `environ` variable.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut environ: *mut *mut c_char = core::ptr::null_mut();

/// Auxiliary vector entry types we use.
pub mod auxv {
    #![allow(missing_docs)]
    pub const AT_NULL: usize = 0;
    pub const AT_PHDR: usize = 3;
    pub const AT_PHENT: usize = 4;
    pub const AT_PHNUM: usize = 5;
    pub const AT_PAGESZ: usize = 6;
    pub const AT_ENTRY: usize = 9;
    pub const AT_UID: usize = 11;
    pub const AT_EUID: usize = 12;
    pub const AT_GID: usize = 13;
    pub const AT_EGID: usize = 14;
    pub const AT_HWCAP: usize = 16;
    pub const AT_CLKTCK: usize = 17;
    pub const AT_SECURE: usize = 23;
    pub const AT_RANDOM: usize = 25;
    pub const AT_HWCAP2: usize = 26;
    pub const AT_EXECFN: usize = 31;
    pub const AT_SYSINFO_EHDR: usize = 33;
}

struct AuxvCell(UnsafeCell<*const usize>);
// SAFETY: written once during single-threaded startup.
unsafe impl Sync for AuxvCell {}
static AUXV: AuxvCell = AuxvCell(UnsafeCell::new(core::ptr::null()));

/// Looks up an auxiliary vector entry (the `getauxval` primitive).
pub fn auxval(kind: usize) -> Option<usize> {
    // SAFETY: only written during startup; entries come in pairs and the
    // kernel terminates the vector with AT_NULL.
    unsafe {
        let mut p = *AUXV.0.get();
        if p.is_null() {
            return None;
        }
        while *p != auxv::AT_NULL {
            if *p == kind {
                return Some(*p.add(1));
            }
            p = p.add(2);
        }
        None
    }
}

/// The C `getauxval` function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getauxval(kind: core::ffi::c_ulong) -> core::ffi::c_ulong {
    match auxval(kind as usize) {
        Some(v) => v as core::ffi::c_ulong,
        None => {
            crate::errno::Errno::ENOENT.set();
            0
        }
    }
}

#[cfg(not(test))]
unsafe extern "C" {
    fn main(argc: c_int, argv: *mut *mut c_char, envp: *mut *mut c_char) -> c_int;
    // Provided by the linker's default script.
    static __preinit_array_start: [Option<unsafe extern "C" fn()>; 0];
    static __preinit_array_end: [Option<unsafe extern "C" fn()>; 0];
    static __init_array_start: [Option<unsafe extern "C" fn()>; 0];
    static __init_array_end: [Option<unsafe extern "C" fn()>; 0];
}

/// Runs the function pointers in `[start, end)` in order.
///
/// # Safety
/// The range must be a valid array of function pointers.
#[cfg(not(test))]
unsafe fn run_array(
    start: *const Option<unsafe extern "C" fn()>,
    end: *const Option<unsafe extern "C" fn()>,
) {
    let mut p = start;
    while p < end {
        // SAFETY: entries are valid function pointers emitted by the linker.
        unsafe {
            if let Some(f) = *p {
                f();
            }
            p = p.add(1);
        }
    }
}

/// Rust-side entry point, called from `_start` with the initial stack
/// pointer (which points at `argc`).
///
/// # Safety
/// Must only be called once, by `_start`.
#[cfg(not(test))]
pub unsafe extern "C" fn start_c(sp: *const usize) -> ! {
    // SAFETY: the kernel lays out argc, argv, NULL, envp, NULL, auxv.
    let (argc, argv, envp) = unsafe {
        let argc = *sp;
        let argv = sp.add(1) as *mut *mut c_char;
        let envp = argv.add(argc + 1);
        let mut p = envp;
        while !(*p).is_null() {
            p = p.add(1);
        }
        *AUXV.0.get() = p.add(1) as *const usize;
        environ = envp;
        (argc, argv, envp)
    };

    // Static TLS and the main thread's TCB.
    // SAFETY: AT_PHDR/AT_PHNUM describe the executable's own headers.
    unsafe {
        let phdr = auxval(auxv::AT_PHDR).unwrap_or(0) as *const tls::Elf64Phdr;
        let phnum = auxval(auxv::AT_PHNUM).unwrap_or(0);
        if !phdr.is_null() {
            tls::init_from_phdrs(phdr, phnum);
        }
    }
    let mut random = [0u8; 8];
    if let Some(p) = auxval(auxv::AT_RANDOM) {
        // SAFETY: AT_RANDOM points at 16 bytes of kernel randomness.
        random.copy_from_slice(unsafe { core::slice::from_raw_parts(p as *const u8, 8) });
    } else if crate::sys::getrandom_exact(&mut random).is_err() {
        crate::exit::abort_now();
    }
    let canary = crate::thread::canary_from_random(random);
    let size = tls::round_up(tls::region_size(), crate::sys::PAGE_SIZE);
    // SAFETY: anonymous private mapping with no address hint.
    let region = unsafe {
        crate::sys::mmap(
            core::ptr::null_mut(),
            size,
            crate::sys::PROT_READ | crate::sys::PROT_WRITE,
            crate::sys::MAP_PRIVATE | crate::sys::MAP_ANONYMOUS,
            -1,
            0,
        )
    };
    let Ok(region) = region else {
        crate::exit::abort_now()
    };
    // SAFETY: the mapping is fresh and large enough.
    let tcb = unsafe { tls::install(region, size, canary) };
    // SAFETY: `tcb` is a fully initialised, self-referencing TCB.
    if unsafe { crate::arch::set_thread_pointer(tcb as *mut u8) }.is_err() {
        crate::exit::abort_now();
    }
    // SAFETY: the TCB is now reachable through the thread pointer.
    unsafe {
        (*tcb).tid.store(
            crate::sys::gettid() as u32,
            core::sync::atomic::Ordering::Relaxed,
        )
    };

    crate::string::simd::init();

    // SAFETY: the linker guarantees these symbol pairs bracket the arrays.
    unsafe {
        run_array(__preinit_array_start.as_ptr(), __preinit_array_end.as_ptr());
        run_array(__init_array_start.as_ptr(), __init_array_end.as_ptr());
    }

    // SAFETY: `main` is provided by the program.
    let status = unsafe { main(argc as c_int, argv, envp) };
    crate::exit::exit(status)
}
