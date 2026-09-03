//! `poll`, `select`, `epoll` and `eventfd`.

use crate::errno::{CReturn, CReturnOr};
use crate::sys::{self, Timespec};
use core::ffi::{c_int, c_long, c_uint, c_void};
use core::ptr;

use crate::arch::nr;

/// `struct pollfd`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PollFd {
    /// Descriptor.
    pub fd: c_int,
    /// Requested events.
    pub events: i16,
    /// Returned events.
    pub revents: i16,
}

/// `poll(2)`.
///
/// # Safety
/// `fds` must point to `n` entries.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn poll(fds: *mut PollFd, n: c_uint, timeout: c_int) -> c_int {
    crate::thread::cancel_point();
    // `ppoll` exists everywhere; `poll` does not (aarch64).
    let ts = sys::Timespec {
        tv_sec: timeout as i64 / 1000,
        tv_nsec: (timeout as i64 % 1000) * 1_000_000,
    };
    let ts_ptr = if timeout < 0 {
        core::ptr::null()
    } else {
        &ts as *const sys::Timespec
    };
    // SAFETY: caller contract; `ts` outlives the call.
    let r = unsafe {
        crate::arch::syscall5(nr::PPOLL, fds as usize, n as usize, ts_ptr as usize, 0, 8)
    };
    crate::thread::cancel_point();
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `ppoll(2)`.
///
/// # Safety
/// `fds` must point to `n` entries; `timeout` and `mask` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ppoll(
    fds: *mut PollFd,
    n: c_uint,
    timeout: *const Timespec,
    mask: *const u64,
) -> c_int {
    crate::thread::cancel_point();
    // The kernel modifies the timeout; pass a copy as glibc does.
    let mut ts = if timeout.is_null() {
        Timespec::default()
    } else {
        // SAFETY: caller contract.
        unsafe { *timeout }
    };
    let tsp = if timeout.is_null() {
        ptr::null_mut()
    } else {
        &mut ts as *mut Timespec
    };
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall5(
            nr::PPOLL,
            fds as usize,
            n as usize,
            tsp as usize,
            mask as usize,
            8,
        )
    };
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `fd_set`: 1024 bits.
#[repr(C)]
pub struct FdSet {
    bits: [c_long; 16],
}

/// Sigmask argument block of `pselect6`.
#[repr(C)]
struct SigMaskArg {
    mask: *const u64,
    size: usize,
}

/// `pselect(2)`.
///
/// # Safety
/// The sets, timeout and mask must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pselect(
    n: c_int,
    r: *mut FdSet,
    w: *mut FdSet,
    e: *mut FdSet,
    timeout: *const Timespec,
    mask: *const u64,
) -> c_int {
    crate::thread::cancel_point();
    let mut ts = if timeout.is_null() {
        Timespec::default()
    } else {
        // SAFETY: caller contract.
        unsafe { *timeout }
    };
    let tsp = if timeout.is_null() {
        ptr::null_mut()
    } else {
        &mut ts as *mut Timespec
    };
    let arg = SigMaskArg { mask, size: 8 };
    // SAFETY: caller contract.
    let ret = unsafe {
        crate::arch::syscall6(
            nr::PSELECT6,
            n as usize,
            r as usize,
            w as usize,
            e as usize,
            tsp as usize,
            &arg as *const SigMaskArg as usize,
        )
    };
    sys::check(ret).map(|v| v as c_int).c_ret_or(-1)
}

/// `struct timeval` for `select`.
#[repr(C)]
pub struct Timeval {
    /// Seconds.
    pub tv_sec: i64,
    /// Microseconds.
    pub tv_usec: i64,
}

/// `select(2)`. The remaining time is written back to `timeout` as on
/// Linux.
///
/// # Safety
/// The sets and timeout must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn select(
    n: c_int,
    r: *mut FdSet,
    w: *mut FdSet,
    e: *mut FdSet,
    timeout: *mut Timeval,
) -> c_int {
    crate::thread::cancel_point();
    let mut ts = Timespec::default();
    let tsp = if timeout.is_null() {
        ptr::null_mut()
    } else {
        // SAFETY: caller contract.
        let tv = unsafe { &*timeout };
        if tv.tv_usec < 0 || tv.tv_usec >= 1_000_000 || tv.tv_sec < 0 {
            crate::errno::Errno::EINVAL.set();
            return -1;
        }
        ts = Timespec {
            tv_sec: tv.tv_sec,
            tv_nsec: tv.tv_usec * 1000,
        };
        &mut ts as *mut Timespec
    };
    // SAFETY: caller contract.
    let ret = unsafe {
        crate::arch::syscall6(
            nr::PSELECT6,
            n as usize,
            r as usize,
            w as usize,
            e as usize,
            tsp as usize,
            0,
        )
    };
    let result = sys::check(ret).map(|v| v as c_int).c_ret_or(-1);
    if !timeout.is_null() {
        // SAFETY: caller contract.
        unsafe {
            *timeout = Timeval {
                tv_sec: ts.tv_sec,
                tv_usec: ts.tv_nsec / 1000,
            }
        };
    }
    result
}

/// `struct epoll_event` (packed on x86_64, naturally aligned elsewhere).
#[cfg_attr(target_arch = "x86_64", repr(C, packed))]
#[cfg_attr(not(target_arch = "x86_64"), repr(C))]
pub struct EpollEvent {
    /// Event mask.
    pub events: u32,
    /// User data.
    pub data: u64,
}

/// `epoll_create1(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn epoll_create1(flags: c_int) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall1(nr::EPOLL_CREATE1, flags as usize) };
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `epoll_create(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn epoll_create(size: c_int) -> c_int {
    if size <= 0 {
        crate::errno::Errno::EINVAL.set();
        return -1;
    }
    epoll_create1(0)
}

/// `epoll_ctl(2)`.
///
/// # Safety
/// `event` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn epoll_ctl(
    epfd: c_int,
    op: c_int,
    fd: c_int,
    event: *mut EpollEvent,
) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall4(
            nr::EPOLL_CTL,
            epfd as usize,
            op as usize,
            fd as usize,
            event as usize,
        )
    };
    sys::check(r).map(drop).c_ret()
}

/// `epoll_pwait(2)`.
///
/// # Safety
/// `events` must point to `max` entries; `mask` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn epoll_pwait(
    epfd: c_int,
    events: *mut EpollEvent,
    max: c_int,
    timeout: c_int,
    mask: *const u64,
) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall6(
            nr::EPOLL_PWAIT,
            epfd as usize,
            events as usize,
            max as usize,
            timeout as usize,
            mask as usize,
            8,
        )
    };
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `epoll_wait(2)`.
///
/// # Safety
/// `events` must point to `max` entries.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn epoll_wait(
    epfd: c_int,
    events: *mut EpollEvent,
    max: c_int,
    timeout: c_int,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { epoll_pwait(epfd, events, max, timeout, ptr::null()) }
}

/// `eventfd_read(3)`.
///
/// # Safety
/// `value` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn eventfd_read(fd: c_int, value: *mut u64) -> c_int {
    // SAFETY: caller contract.
    match unsafe { sys::read(fd, value as *mut u8, 8) } {
        Ok(8) => 0,
        Ok(_) => {
            crate::errno::Errno::EIO.set();
            -1
        }
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `eventfd_write(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn eventfd_write(fd: c_int, value: u64) -> c_int {
    // SAFETY: the value is on the stack.
    match unsafe { sys::write(fd, &value as *const u64 as *const u8, 8) } {
        Ok(8) => 0,
        Ok(_) => {
            crate::errno::Errno::EIO.set();
            -1
        }
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// Keeps `c_void` referenced for header-facing signatures.
#[allow(dead_code)]
fn _void(_: *mut c_void) {}
