//! `<link.h>` and `<dlfcn.h>` for a static executable, plus the C++
//! runtime hooks (`__cxa_atexit`, `__cxa_finalize`, `__dso_handle`,
//! `__cxa_thread_atexit_impl`).
//!
//! `dl_iterate_phdr` reports the executable's own program headers, which
//! is what libgcc's unwinder needs to find `.eh_frame_hdr` for C++
//! exceptions and backtraces. Dynamic loading is not supported: `dlopen`
//! fails and `dlerror` explains why.

use crate::c_char;
use crate::malloc;
use crate::thread::tls::Elf64Phdr;
use core::ffi::{c_int, c_void};
use core::ptr;

/// `struct dl_phdr_info`.
#[allow(missing_docs)]
#[repr(C)]
pub struct DlPhdrInfo {
    pub dlpi_addr: usize,
    pub dlpi_name: *const c_char,
    pub dlpi_phdr: *const Elf64Phdr,
    pub dlpi_phnum: u16,
    pub dlpi_adds: u64,
    pub dlpi_subs: u64,
    pub dlpi_tls_modid: usize,
    pub dlpi_tls_data: *mut c_void,
}

type PhdrCallback = unsafe extern "C" fn(*mut DlPhdrInfo, usize, *mut c_void) -> c_int;

/// `dl_iterate_phdr(3)`.
///
/// # Safety
/// `callback` must be a valid function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn dl_iterate_phdr(callback: PhdrCallback, data: *mut c_void) -> c_int {
    let phdr = crate::start::auxval(crate::start::auxv::AT_PHDR).unwrap_or(0) as *const Elf64Phdr;
    let phnum = crate::start::auxval(crate::start::auxv::AT_PHNUM).unwrap_or(0);
    if phdr.is_null() {
        return 0;
    }
    let mut info = DlPhdrInfo {
        // Zero for a non-PIE executable; a static PIE recorded its load
        // bias when it relocated itself.
        dlpi_addr: crate::start::load_bias(),
        dlpi_name: c"".as_ptr(),
        dlpi_phdr: phdr,
        dlpi_phnum: phnum as u16,
        dlpi_adds: 1,
        dlpi_subs: 0,
        dlpi_tls_modid: 1,
        dlpi_tls_data: ptr::null_mut(),
    };
    // SAFETY: caller contract.
    unsafe { callback(&mut info, core::mem::size_of::<DlPhdrInfo>(), data) }
}

/// `dlopen(3)`: always fails.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dlopen(_name: *const c_char, _flags: c_int) -> *mut c_void {
    ptr::null_mut()
}

/// `dlsym(3)`: always fails.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dlsym(_handle: *mut c_void, _name: *const c_char) -> *mut c_void {
    ptr::null_mut()
}

/// `dlclose(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dlclose(_handle: *mut c_void) -> c_int {
    0
}

/// `dlerror(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dlerror() -> *mut c_char {
    c"dynamic loading is not supported by this static libc".as_ptr() as *mut c_char
}

/// `__dso_handle`: the address identifies "this DSO" in `__cxa_atexit`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub static __dso_handle: usize = 0;

/// `__cxa_atexit`: registers `func(arg)` to run at `exit`.
///
/// # Safety
/// `func` must be a valid function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __cxa_atexit(
    func: unsafe extern "C" fn(*mut c_void),
    arg: *mut c_void,
    _dso: *mut c_void,
) -> c_int {
    crate::exit::register_with_arg(func, arg)
}

/// `__cxa_finalize`: with a null DSO handle runs all handlers; there is
/// nothing to unload otherwise.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __cxa_finalize(dso: *mut c_void) {
    if dso.is_null() {
        crate::exit::run_atexit();
    }
}

/// A registered thread-local destructor.
#[repr(C)]
pub struct ThreadDtor {
    func: unsafe extern "C" fn(*mut c_void),
    obj: *mut c_void,
    next: *mut ThreadDtor,
}

/// `__cxa_thread_atexit_impl`: destructors for C++ `thread_local`
/// objects, run when the thread exits (before TSD destructors).
///
/// # Safety
/// `func` must be a valid function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __cxa_thread_atexit_impl(
    func: unsafe extern "C" fn(*mut c_void),
    obj: *mut c_void,
    _dso: *mut c_void,
) -> c_int {
    let node = malloc::alloc(core::mem::size_of::<ThreadDtor>()) as *mut ThreadDtor;
    if node.is_null() {
        return -1;
    }
    let tcb = crate::thread::current();
    // SAFETY: fresh block; the TCB is valid.
    unsafe {
        node.write(ThreadDtor {
            func,
            obj,
            next: (*tcb).thread_dtors,
        });
        (*tcb).thread_dtors = node;
    }
    0
}

/// Runs and frees the calling thread's `thread_local` destructors.
pub fn run_thread_dtors() {
    let tcb = crate::thread::current();
    loop {
        // SAFETY: the TCB is valid; nodes are our own blocks.
        unsafe {
            let node = (*tcb).thread_dtors;
            if node.is_null() {
                break;
            }
            (*tcb).thread_dtors = (*node).next;
            ((*node).func)((*node).obj);
            malloc::dealloc(node as *mut u8);
        }
    }
}
