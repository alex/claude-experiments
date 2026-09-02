//! `<signal.h>`.
//!
//! `sigset_t` is 128 bytes as in glibc/musl (only the first 64 bits are
//! used on Linux). The user-visible `struct sigaction` is converted to the
//! kernel layout in [`sigaction`], which always installs our
//! `rt_sigreturn` trampoline as the restorer.

use crate::c_char;
use crate::errno::{CReturn, Errno};
use crate::sys::{
    self, KernelSigaction, NSIG, SA_RESTART, SA_RESTORER, SIG_BLOCK, SIG_SETMASK, SIG_UNBLOCK,
    Timespec,
};
use core::ffi::{c_int, c_long, c_uint, c_void};
use core::ptr;

/// `sigset_t`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SigSet {
    bits: [u64; 16],
}

impl SigSet {
    /// The empty set.
    pub const fn empty() -> Self {
        SigSet { bits: [0; 16] }
    }
}

/// The user-visible `struct sigaction`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SigAction {
    /// `sa_handler` / `sa_sigaction`.
    pub handler: usize,
    /// `sa_mask`.
    pub mask: SigSet,
    /// `sa_flags`.
    pub flags: c_int,
    /// `sa_restorer` (ignored; ours is always used).
    pub restorer: usize,
}

/// `SIG_DFL`.
pub const SIG_DFL: usize = 0;
/// `SIG_IGN`.
pub const SIG_IGN: usize = 1;
/// `SIG_ERR`.
pub const SIG_ERR: usize = usize::MAX;

#[cfg(not(test))]
unsafe extern "C" {
    fn __rustlibc_restore_rt();
}

#[cfg(not(test))]
fn restorer() -> usize {
    __rustlibc_restore_rt as *const () as usize
}

#[cfg(test)]
fn restorer() -> usize {
    0
}

/// Signals reserved for the implementation (thread cancellation and one
/// spare, as in glibc and musl): programs cannot install handlers for
/// them or block them.
const RESERVED_MASK: u64 = 0b11 << 31; // signals 32 and 33

fn valid(sig: c_int) -> bool {
    (1..NSIG).contains(&sig) && RESERVED_MASK & (1u64 << (sig - 1)) == 0
}

/// Installs a handler for an internal signal (`SA_SIGINFO`, no
/// `SA_RESTART` so that blocking calls return `EINTR`).
pub(crate) fn install_internal_handler(sig: c_int, handler: usize) {
    let act = KernelSigaction {
        handler,
        flags: crate::sys::SA_SIGINFO | SA_RESTORER,
        restorer: restorer(),
        mask: 0,
    };
    // SAFETY: valid action structure.
    let _ = unsafe { sys::rt_sigaction(sig, &act, ptr::null_mut()) };
}

/// A copy of `set` with the reserved signals cleared, for `SIG_BLOCK`
/// and `SIG_SETMASK` (null stays null).
///
/// # Safety
/// `set` must be null or valid.
pub(crate) unsafe fn strip_internal(how: c_int, set: *const u64) -> Option<u64> {
    if set.is_null() {
        return None;
    }
    // SAFETY: caller contract.
    let mut v = unsafe { *set };
    if how != SIG_UNBLOCK {
        v &= !RESERVED_MASK;
    }
    Some(v)
}

/// `sigemptyset(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigemptyset(set: *mut SigSet) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*set).bits = [0; 16] };
    0
}

/// `sigfillset(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigfillset(set: *mut SigSet) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        (*set).bits = [0; 16];
        (*set).bits[0] = u64::MAX;
    }
    0
}

/// `sigaddset(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigaddset(set: *mut SigSet, sig: c_int) -> c_int {
    if !valid(sig) {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe { (*set).bits[0] |= 1 << (sig - 1) };
    0
}

/// `sigdelset(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigdelset(set: *mut SigSet, sig: c_int) -> c_int {
    if !valid(sig) {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe { (*set).bits[0] &= !(1 << (sig - 1)) };
    0
}

/// `sigismember(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigismember(set: *const SigSet, sig: c_int) -> c_int {
    if !valid(sig) {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    (unsafe { (*set).bits[0] } >> (sig - 1) & 1) as c_int
}

/// `sigisemptyset(3)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigisemptyset(set: *const SigSet) -> c_int {
    // SAFETY: caller contract.
    (unsafe { (*set).bits[0] } == 0) as c_int
}

/// `sigaction(2)`.
///
/// # Safety
/// `act` and `old` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigaction(
    sig: c_int,
    act: *const SigAction,
    old: *mut SigAction,
) -> c_int {
    // SIGKILL and SIGSTOP can be queried but not changed.
    if !valid(sig) || ((sig == sys::SIGKILL || sig == sys::SIGSTOP) && !act.is_null()) {
        Errno::EINVAL.set();
        return -1;
    }
    let mut kold = KernelSigaction::default();
    // SAFETY: caller contract.
    let knew = unsafe { act.as_ref() }.map(|a| KernelSigaction {
        handler: a.handler,
        flags: (a.flags as u32 as u64) | SA_RESTORER,
        restorer: restorer(),
        mask: a.mask.bits[0],
    });
    let knew_ptr = knew
        .as_ref()
        .map_or(ptr::null(), |k| k as *const KernelSigaction);
    // SAFETY: valid kernel structures.
    if let Err(e) = unsafe {
        sys::rt_sigaction(
            sig,
            knew_ptr,
            if old.is_null() {
                ptr::null_mut()
            } else {
                &mut kold
            },
        )
    } {
        e.set();
        return -1;
    }
    if !old.is_null() {
        // SAFETY: caller contract.
        unsafe {
            *old = SigAction {
                handler: kold.handler,
                mask: SigSet {
                    bits: [kold.mask, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                },
                flags: (kold.flags & !SA_RESTORER) as c_int,
                restorer: kold.restorer,
            };
        }
    }
    0
}

/// `signal(2)` with BSD semantics (`SA_RESTART`, handler stays installed).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn signal(sig: c_int, handler: usize) -> usize {
    let act = SigAction {
        handler,
        mask: SigSet { bits: [0; 16] },
        flags: SA_RESTART as c_int,
        restorer: 0,
    };
    let mut old = act;
    // SAFETY: valid pointers.
    if unsafe { sigaction(sig, &act, &mut old) } < 0 {
        SIG_ERR
    } else {
        old.handler
    }
}

/// `sigprocmask(2)`.
///
/// # Safety
/// `set` and `old` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigprocmask(how: c_int, set: *const SigSet, old: *mut SigSet) -> c_int {
    if !set.is_null() && !matches!(how, SIG_BLOCK | SIG_UNBLOCK | SIG_SETMASK) {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract; the kernel only reads/writes 8 bytes.
    unsafe {
        let stripped = strip_internal(
            how,
            if set.is_null() {
                ptr::null()
            } else {
                &(*set).bits[0]
            },
        );
        let set_ptr = stripped.as_ref().map_or(ptr::null(), |s| s as *const u64);
        let mut kold = 0u64;
        let r = sys::rt_sigprocmask(
            how,
            set_ptr,
            if old.is_null() {
                ptr::null_mut()
            } else {
                &mut kold
            },
        );
        if r.is_ok() && !old.is_null() {
            (*old).bits = [0; 16];
            (*old).bits[0] = kold;
        }
        r.c_ret()
    }
}

/// `kill(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn kill(pid: c_int, sig: c_int) -> c_int {
    sys::kill(pid, sig).c_ret()
}

/// `killpg(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn killpg(pgrp: c_int, sig: c_int) -> c_int {
    if pgrp <= 0 {
        Errno::EINVAL.set();
        return -1;
    }
    kill(-pgrp, sig)
}

/// `raise(3)`: delivers the signal to the calling thread.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn raise(sig: c_int) -> c_int {
    sys::tgkill(sys::getpid(), sys::gettid(), sig).c_ret()
}

/// `pause(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pause() -> c_int {
    crate::thread::cancel_point();
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall0(crate::arch::nr::PAUSE) };
    sys::check(r).map(drop).c_ret()
}

/// `sigsuspend(2)`.
///
/// # Safety
/// `mask` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigsuspend(mask: *const SigSet) -> c_int {
    crate::thread::cancel_point();
    // SAFETY: caller contract; the kernel reads 8 bytes.
    let r = unsafe {
        crate::arch::syscall2(
            crate::arch::nr::RT_SIGSUSPEND,
            &(*mask).bits[0] as *const u64 as usize,
            8,
        )
    };
    sys::check(r).map(drop).c_ret()
}

/// `sigpending(2)`.
///
/// # Safety
/// `set` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigpending(set: *mut SigSet) -> c_int {
    let mut bits = 0u64;
    // SAFETY: valid pointer.
    let r = unsafe {
        crate::arch::syscall2(
            crate::arch::nr::RT_SIGPENDING,
            &mut bits as *mut u64 as usize,
            8,
        )
    };
    match sys::check(r) {
        Ok(_) => {
            // SAFETY: caller contract.
            unsafe {
                (*set).bits = [0; 16];
                (*set).bits[0] = bits;
            }
            0
        }
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `sigtimedwait(2)`.
///
/// # Safety
/// `set` must be valid; `info` and `timeout` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigtimedwait(
    set: *const SigSet,
    info: *mut c_void,
    timeout: *const Timespec,
) -> c_int {
    // SAFETY: caller contract; the kernel reads 8 bytes of the set.
    let r = unsafe {
        crate::arch::syscall4(
            crate::arch::nr::RT_SIGTIMEDWAIT,
            &(*set).bits[0] as *const u64 as usize,
            info as usize,
            timeout as usize,
            8,
        )
    };
    sys::check(r).map(|v| v as c_int).c_ret()
}

/// `sigwaitinfo(2)`.
///
/// # Safety
/// As for [`sigtimedwait`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigwaitinfo(set: *const SigSet, info: *mut c_void) -> c_int {
    // SAFETY: forwarded.
    unsafe { sigtimedwait(set, info, ptr::null()) }
}

/// `sigwait(3)`: returns an error number rather than setting `errno`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigwait(set: *const SigSet, sig: *mut c_int) -> c_int {
    crate::thread::cancel_point();
    loop {
        // SAFETY: forwarded.
        let r = unsafe { sigtimedwait(set, ptr::null_mut(), ptr::null()) };
        if r >= 0 {
            // SAFETY: caller contract.
            unsafe { *sig = r };
            return 0;
        }
        let e = Errno::get();
        if e != Errno::EINTR {
            return e.0;
        }
    }
}

/// `alarm(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn alarm(seconds: c_uint) -> c_uint {
    // SAFETY: no memory is involved.
    unsafe { crate::arch::syscall1(crate::arch::nr::ALARM, seconds as usize) as c_uint }
}

/// `stack_t`.
#[repr(C)]
pub struct StackT {
    /// Base of the stack.
    pub ss_sp: *mut c_void,
    /// `SS_ONSTACK` / `SS_DISABLE`.
    pub ss_flags: c_int,
    /// Size of the stack.
    pub ss_size: usize,
}

/// `sigaltstack(2)`.
///
/// # Safety
/// Both pointers must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sigaltstack(new: *const StackT, old: *mut StackT) -> c_int {
    // SAFETY: caller contract; the layout matches the kernel's.
    let r =
        unsafe { crate::arch::syscall2(crate::arch::nr::SIGALTSTACK, new as usize, old as usize) };
    sys::check(r).map(drop).c_ret()
}

/// `siginterrupt(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn siginterrupt(sig: c_int, flag: c_int) -> c_int {
    let mut act = SigAction {
        handler: 0,
        mask: SigSet { bits: [0; 16] },
        flags: 0,
        restorer: 0,
    };
    // SAFETY: valid pointers.
    unsafe {
        if sigaction(sig, ptr::null(), &mut act) < 0 {
            return -1;
        }
        if flag != 0 {
            act.flags &= !(SA_RESTART as c_int);
        } else {
            act.flags |= SA_RESTART as c_int;
        }
        sigaction(sig, &act, ptr::null_mut())
    }
}

/// Descriptions for `strsignal`.
static SIGNAL_NAMES: [&str; 32] = [
    "Unknown signal 0\0",
    "Hangup\0",
    "Interrupt\0",
    "Quit\0",
    "Illegal instruction\0",
    "Trace/breakpoint trap\0",
    "Aborted\0",
    "Bus error\0",
    "Floating point exception\0",
    "Killed\0",
    "User defined signal 1\0",
    "Segmentation fault\0",
    "User defined signal 2\0",
    "Broken pipe\0",
    "Alarm clock\0",
    "Terminated\0",
    "Stack fault\0",
    "Child exited\0",
    "Continued\0",
    "Stopped (signal)\0",
    "Stopped\0",
    "Stopped (tty input)\0",
    "Stopped (tty output)\0",
    "Urgent I/O condition\0",
    "CPU time limit exceeded\0",
    "File size limit exceeded\0",
    "Virtual timer expired\0",
    "Profiling timer expired\0",
    "Window changed\0",
    "I/O possible\0",
    "Power failure\0",
    "Bad system call\0",
];

/// `strsignal(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn strsignal(sig: c_int) -> *mut c_char {
    if let Some(name) = usize::try_from(sig).ok().and_then(|i| SIGNAL_NAMES.get(i)) {
        return name.as_ptr() as *mut c_char;
    }
    // SAFETY: the TCB is valid for the life of the thread.
    let buf = unsafe { &mut (*crate::thread::current()).strerror_buf };
    let mut w = crate::fmt::SliceWriter::new(buf);
    let _ = if valid(sig) {
        core::fmt::write(&mut w, format_args!("Real-time signal {}", sig - 32))
    } else {
        core::fmt::write(&mut w, format_args!("Unknown signal {sig}"))
    };
    let len = w.len();
    buf[len] = 0;
    buf.as_mut_ptr() as *mut c_char
}

/// `psignal(3)`.
///
/// # Safety
/// `prefix` must be null or NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn psignal(sig: c_int, prefix: *const c_char) {
    // SAFETY: stderr is always valid.
    let mut g = unsafe { crate::stdio::lock(crate::stdio::stderr) };
    let mut out = crate::stdio::printf::Staged::new(&mut g);
    use crate::stdio::printf::Sink;
    if !prefix.is_null() {
        // SAFETY: caller contract.
        let p = unsafe {
            core::slice::from_raw_parts(
                prefix as *const u8,
                crate::string::search::strlen(prefix as *const u8),
            )
        };
        if !p.is_empty() {
            out.write(p);
            out.write(b": ");
        }
    }
    let msg = strsignal(sig);
    // SAFETY: strsignal returns NUL-terminated strings.
    out.write(unsafe {
        core::slice::from_raw_parts(
            msg as *const u8,
            crate::string::search::strlen(msg as *const u8),
        )
    });
    out.write(b"\n");
    out.finish();
}

/// The second half of `sigsetjmp` (see the assembly in `arch`): on the
/// first return saves the signal mask into the buffer, on returns through
/// `siglongjmp` restores it. `sigsetjmp(buf, 0)` never comes through
/// here, so no flag is needed. Slot 8 of the buffer holds the caller's
/// return address for the `siglongjmp` path and must not be touched.
///
/// # Safety
/// Called only from the assembly stub with a valid `jmp_buf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __sigsetjmp_tail(jb: *mut c_long, ret: c_int) -> c_int {
    // SAFETY: the buffer has 8 register words, a stash word and 16 mask
    // words; only the first mask word is used.
    unsafe {
        let mask = jb.add(9) as *mut u64;
        if ret == 0 {
            let _ = sys::rt_sigprocmask(SIG_BLOCK, ptr::null(), mask);
        } else {
            let _ = sys::rt_sigprocmask(SIG_SETMASK, mask, ptr::null_mut());
        }
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sets() {
        let mut s = SigSet { bits: [0xff; 16] };
        // SAFETY: valid pointer.
        unsafe {
            assert_eq!(sigemptyset(&mut s), 0);
            assert_eq!(sigisemptyset(&s), 1);
            assert_eq!(sigaddset(&mut s, 2), 0);
            assert_eq!(sigaddset(&mut s, 64), 0);
            assert_eq!(sigaddset(&mut s, 65), -1);
            assert_eq!(sigaddset(&mut s, 0), -1);
            assert_eq!(sigismember(&s, 2), 1);
            assert_eq!(sigismember(&s, 3), 0);
            assert_eq!(sigismember(&s, 64), 1);
            assert_eq!(sigdelset(&mut s, 2), 0);
            assert_eq!(sigismember(&s, 2), 0);
            assert_eq!(sigfillset(&mut s), 0);
            assert_eq!(sigismember(&s, 31), 1);
        }
    }

    #[test]
    fn names() {
        // SAFETY: NUL-terminated results.
        unsafe {
            assert_eq!(
                std::ffi::CStr::from_ptr(strsignal(11)).to_str().unwrap(),
                "Segmentation fault"
            );
            assert_eq!(
                std::ffi::CStr::from_ptr(strsignal(40)).to_str().unwrap(),
                "Real-time signal 8"
            );
            assert_eq!(
                std::ffi::CStr::from_ptr(strsignal(99)).to_str().unwrap(),
                "Unknown signal 99"
            );
        }
    }
}
