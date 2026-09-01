//! Threads: the thread control block, static TLS and (later) pthreads.

use core::ffi::c_int;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

pub mod pthread;
pub mod sync;
pub mod tls;

/// Maximum number of thread-specific data keys.
pub const KEYS_MAX: usize = 128;

/// Thread state (`Tcb::state`): joinable and running.
pub const STATE_JOINABLE: u32 = 0;
/// Thread state: detached.
pub const STATE_DETACHED: u32 = 1;
/// Thread state: exited while joinable; the joiner reclaims it.
pub const STATE_EXITED: u32 = 2;

/// A `pthread_cleanup_push` record (matches `struct __ptcb` in the
/// header).
#[repr(C)]
pub struct CleanupRecord {
    /// The handler.
    pub func: Option<unsafe extern "C" fn(*mut core::ffi::c_void)>,
    /// Its argument.
    pub arg: *mut core::ffi::c_void,
    /// The previously pushed record.
    pub next: *mut CleanupRecord,
}

/// Set once the process has created a second thread. Until then locks
/// that only guard against other threads can be skipped.
static THREADED: AtomicBool = AtomicBool::new(false);

/// True once more than one thread may exist.
#[inline(always)]
pub fn is_threaded() -> bool {
    THREADED.load(Ordering::Relaxed)
}

/// Marks the process as multi-threaded (before the first `clone`).
pub fn set_threaded() {
    THREADED.store(true, Ordering::Release);
}

/// Kernel thread id of the calling thread.
#[inline(always)]
pub fn tid() -> u32 {
    // SAFETY: the current thread's TCB is always valid.
    unsafe { (*current()).tid.load(Ordering::Relaxed) }
}

/// The thread control block (TCB).
///
/// The thread pointer register (`%fs` on x86_64) points at this structure
/// for every thread. The first seven words are dictated by the psABI and
/// compiler conventions and must not move:
///
/// * word 0 must point to the TCB itself (`%fs:0` is how code finds it),
/// * word 5 (offset 0x28) is the `-fstack-protector` canary,
/// * word 6 (offset 0x30) is glibc's pointer guard (unused, kept for
///   layout compatibility with code that hard-codes the offset).
///
/// The static TLS block of the executable sits immediately *below* the
/// TCB (TLS variant II), see [`tls`].
#[repr(C)]
pub struct Tcb {
    /// Self pointer; must be the first field.
    pub self_ptr: *mut Tcb,
    dtv: usize,
    self_ptr2: *mut Tcb,
    multiple_threads: usize,
    sysinfo: usize,
    /// The stack protector canary.
    pub stack_guard: usize,
    pointer_guard: usize,

    /// The C `errno` of this thread.
    pub errno: c_int,
    /// Scratch buffer for `strerror` of unknown error numbers.
    pub strerror_buf: [u8; 32],
    /// State of `strtok`.
    pub strtok_save: *mut crate::c_char,
    /// Result buffer of `gmtime`/`localtime`.
    pub tm: crate::time::Tm,
    /// Result buffer of `asctime`/`ctime`.
    pub asctime_buf: [u8; 26],
    /// Result buffer of `ttyname`.
    pub path_buf: [u8; 256],
    /// The thread's allocator state.
    pub heap: crate::malloc::Heap,
    /// Kernel thread id. Cleared by the kernel (and a futex wake issued)
    /// when the thread exits, because it is registered as the
    /// `CLONE_CHILD_CLEARTID` address.
    pub tid: AtomicU32,

    /// Base of the thread's stack mapping (null for the main thread).
    pub map_base: *mut u8,
    /// Length of the stack mapping.
    pub map_len: usize,
    /// `STATE_*`.
    pub state: AtomicU32,
    /// The thread's start routine.
    pub start: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut core::ffi::c_void>,
    /// Argument for `start`.
    pub arg: *mut core::ffi::c_void,
    /// Return value of the thread.
    pub result: *mut core::ffi::c_void,
    /// Innermost cleanup handler.
    pub cleanup: *mut CleanupRecord,
    /// Thread-specific data values.
    pub keys: [*mut core::ffi::c_void; KEYS_MAX],
}

impl Tcb {
    /// Initialises a TCB in place at `tcb`.
    ///
    /// # Safety
    /// `tcb` must be valid, suitably aligned and not yet in use.
    pub unsafe fn init(tcb: *mut Tcb, canary: usize) {
        // SAFETY: caller guarantees `tcb` is valid and unaliased.
        unsafe {
            tcb.write(Tcb {
                self_ptr: tcb,
                dtv: 0,
                self_ptr2: tcb,
                multiple_threads: 0,
                sysinfo: 0,
                stack_guard: canary,
                pointer_guard: 0,
                errno: 0,
                strerror_buf: [0; 32],
                strtok_save: core::ptr::null_mut(),
                tm: crate::time::Tm::default(),
                asctime_buf: [0; 26],
                path_buf: [0; 256],
                heap: crate::malloc::Heap::new(),
                tid: AtomicU32::new(0),
                map_base: core::ptr::null_mut(),
                map_len: 0,
                state: AtomicU32::new(STATE_JOINABLE),
                start: None,
                arg: core::ptr::null_mut(),
                result: core::ptr::null_mut(),
                cleanup: core::ptr::null_mut(),
                keys: [core::ptr::null_mut(); KEYS_MAX],
            });
        }
    }
}

/// Returns the TCB of the calling thread.
#[cfg(not(test))]
#[inline(always)]
pub fn current() -> *mut Tcb {
    // SAFETY: the thread pointer is set before any Rust code runs.
    unsafe { crate::arch::thread_pointer() as *mut Tcb }
}

/// Host-test stand-in: a `thread_local!` TCB, because the real thread
/// pointer belongs to the host libc.
#[cfg(test)]
pub fn current() -> *mut Tcb {
    use std::cell::UnsafeCell;
    // Host tests run several threads at once.
    THREADED.store(true, Ordering::Relaxed);
    struct Slot(
        UnsafeCell<core::mem::MaybeUninit<Tcb>>,
        core::cell::Cell<bool>,
    );
    thread_local! { static TCB: Slot = Slot(UnsafeCell::new(core::mem::MaybeUninit::uninit()), core::cell::Cell::new(false)); }
    TCB.with(|slot| {
        let p = slot.0.get() as *mut Tcb;
        if !slot.1.get() {
            // SAFETY: initialised exactly once per thread.
            unsafe {
                Tcb::init(p, 0);
                (*p).tid
                    .store(crate::sys::gettid() as u32, Ordering::Relaxed);
            }
            slot.1.set(true);
        }
        p
    })
}

/// Derives a stack protector canary from `random`, forcing the lowest byte
/// to zero so that string based overflows cannot copy the whole canary.
pub fn canary_from_random(random: [u8; 8]) -> usize {
    usize::from_ne_bytes(random) & !0xff
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abi_offsets() {
        assert_eq!(core::mem::offset_of!(Tcb, self_ptr), 0);
        assert_eq!(core::mem::offset_of!(Tcb, stack_guard), 0x28);
        assert_eq!(core::mem::offset_of!(Tcb, pointer_guard), 0x30);
    }

    #[test]
    fn canary_low_byte_is_zero() {
        assert_eq!(canary_from_random([0xff; 8]) & 0xff, 0);
        assert_ne!(canary_from_random([0xff; 8]), 0);
    }
}
