//! POSIX process and file descriptor primitives from `<unistd.h>`.

use crate::errno::CReturn;
use crate::sys;
use core::ffi::{c_int, c_void};

/// `write(2)`.
///
/// # Safety
/// `buf` must be valid for reads of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn write(fd: c_int, buf: *const c_void, count: usize) -> isize {
    // SAFETY: forwarded from the caller.
    unsafe { sys::write(fd, buf as *const u8, count) }.c_ret()
}

/// `read(2)`.
///
/// # Safety
/// `buf` must be valid for writes of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn read(fd: c_int, buf: *mut c_void, count: usize) -> isize {
    // SAFETY: forwarded from the caller.
    unsafe { sys::read(fd, buf as *mut u8, count) }.c_ret()
}

/// `close(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn close(fd: c_int) -> c_int {
    sys::close(fd).c_ret()
}

/// `getpid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpid() -> c_int {
    sys::getpid()
}

/// `gettid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn gettid() -> c_int {
    sys::gettid()
}
