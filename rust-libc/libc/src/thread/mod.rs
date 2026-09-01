//! Threads: the thread control block, static TLS and (later) pthreads.

use core::ffi::c_int;
use core::sync::atomic::AtomicU32;

pub mod tls;

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
    /// Kernel thread id. Cleared by the kernel (and a futex wake issued)
    /// when the thread exits, because it is registered as the
    /// `CLONE_CHILD_CLEARTID` address.
    pub tid: AtomicU32,
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
                tid: AtomicU32::new(0),
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
    struct Slot(
        UnsafeCell<core::mem::MaybeUninit<Tcb>>,
        core::cell::Cell<bool>,
    );
    thread_local! { static TCB: Slot = Slot(UnsafeCell::new(core::mem::MaybeUninit::uninit()), core::cell::Cell::new(false)); }
    TCB.with(|slot| {
        let p = slot.0.get() as *mut Tcb;
        if !slot.1.get() {
            // SAFETY: initialised exactly once per thread.
            unsafe { Tcb::init(p, 0) };
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
