//! `<termios.h>` and pseudo-terminals.
//!
//! `struct termios` uses the kernel layout (`NCCS = 32`, plus the two
//! speed fields musl and glibc append); `TCGETS`/`TCSETS` only touch the
//! first 36 bytes.

use crate::c_char;
use crate::errno::{CReturn, Errno};
use crate::sys;
use core::ffi::{c_int, c_uint};

/// `struct termios`.
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Termios {
    pub c_iflag: c_uint,
    pub c_oflag: c_uint,
    pub c_cflag: c_uint,
    pub c_lflag: c_uint,
    pub c_line: u8,
    pub c_cc: [u8; 32],
    pub c_ispeed: c_uint,
    pub c_ospeed: c_uint,
}

const TCGETS: usize = 0x5401;
const TCSETS: usize = 0x5402;
const TCFLSH: usize = 0x540b;
const TCSBRK: usize = 0x5409;
const TCSBRKP: usize = 0x5425;
const TCXONC: usize = 0x540a;
const TIOCGPGRP: usize = 0x540f;
const TIOCSPGRP: usize = 0x5410;
const TIOCGSID: usize = 0x5429;
const CBAUD: c_uint = 0o10017;

fn ioctl(fd: c_int, req: usize, arg: usize) -> c_int {
    // SAFETY: the callers pass valid arguments for each request.
    unsafe { sys::ioctl(fd, req, arg) }.map(drop).c_ret()
}

/// `tcgetattr(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tcgetattr(fd: c_int, t: *mut Termios) -> c_int {
    let r = ioctl(fd, TCGETS, t as usize);
    if r == 0 {
        // SAFETY: caller contract.
        unsafe {
            (*t).c_ispeed = (*t).c_cflag & CBAUD;
            (*t).c_ospeed = (*t).c_cflag & CBAUD;
        }
    }
    r
}

/// `tcsetattr(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tcsetattr(fd: c_int, action: c_int, t: *const Termios) -> c_int {
    if !(0..=2).contains(&action) {
        Errno::EINVAL.set();
        return -1;
    }
    ioctl(fd, TCSETS + action as usize, t as usize)
}

/// `cfgetospeed(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfgetospeed(t: *const Termios) -> c_uint {
    // SAFETY: caller contract.
    unsafe { (*t).c_cflag & CBAUD }
}

/// `cfgetispeed(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfgetispeed(t: *const Termios) -> c_uint {
    // SAFETY: forwarded.
    unsafe { cfgetospeed(t) }
}

/// `cfsetospeed(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfsetospeed(t: *mut Termios, speed: c_uint) -> c_int {
    if speed & !CBAUD != 0 {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe {
        (*t).c_cflag = ((*t).c_cflag & !CBAUD) | speed;
        (*t).c_ospeed = speed;
        (*t).c_ispeed = speed;
    }
    0
}

/// `cfsetispeed(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfsetispeed(t: *mut Termios, speed: c_uint) -> c_int {
    if speed == 0 {
        return 0;
    }
    // SAFETY: forwarded.
    unsafe { cfsetospeed(t, speed) }
}

/// `cfsetspeed(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfsetspeed(t: *mut Termios, speed: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { cfsetospeed(t, speed) }
}

/// `cfmakeraw(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cfmakeraw(t: *mut Termios) {
    // SAFETY: caller contract.
    unsafe {
        // IGNBRK BRKINT PARMRK ISTRIP INLCR IGNCR ICRNL IXON
        (*t).c_iflag &= !(0o1 | 0o2 | 0o10 | 0o40 | 0o100 | 0o200 | 0o400 | 0o2000);
        (*t).c_oflag &= !0o1; // OPOST
        // ECHO ECHONL ICANON ISIG IEXTEN
        (*t).c_lflag &= !(0o10 | 0o100 | 0o2 | 0o1 | 0o100000);
        (*t).c_cflag &= !(0o60 | 0o400); // CSIZE PARENB
        (*t).c_cflag |= 0o60; // CS8
        (*t).c_cc[6] = 1; // VMIN
        (*t).c_cc[5] = 0; // VTIME
    }
}

/// `tcflush(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcflush(fd: c_int, queue: c_int) -> c_int {
    ioctl(fd, TCFLSH, queue as usize)
}

/// `tcdrain(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcdrain(fd: c_int) -> c_int {
    ioctl(fd, TCSBRK, 1)
}

/// `tcsendbreak(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcsendbreak(fd: c_int, _duration: c_int) -> c_int {
    ioctl(fd, TCSBRKP, 0)
}

/// `tcflow(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcflow(fd: c_int, action: c_int) -> c_int {
    ioctl(fd, TCXONC, action as usize)
}

/// `tcgetpgrp(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcgetpgrp(fd: c_int) -> c_int {
    let mut pgrp: c_int = 0;
    if ioctl(fd, TIOCGPGRP, &mut pgrp as *mut c_int as usize) < 0 {
        return -1;
    }
    pgrp
}

/// `tcsetpgrp(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcsetpgrp(fd: c_int, pgrp: c_int) -> c_int {
    ioctl(fd, TIOCSPGRP, &pgrp as *const c_int as usize)
}

/// `tcgetsid(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tcgetsid(fd: c_int) -> c_int {
    let mut sid: c_int = 0;
    if ioctl(fd, TIOCGSID, &mut sid as *mut c_int as usize) < 0 {
        return -1;
    }
    sid
}

// ---------------------------------------------------------------------
// Pseudo-terminals.

const TIOCSPTLCK: usize = 0x4004_5431;
const TIOCGPTN: usize = 0x8004_5430;

/// `posix_openpt(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn posix_openpt(flags: c_int) -> c_int {
    // SAFETY: literal path.
    unsafe { crate::fs::open(c"/dev/ptmx".as_ptr(), flags, 0) }
}

/// `grantpt(3)`: nothing to do with devpts.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn grantpt(_fd: c_int) -> c_int {
    0
}

/// `unlockpt(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn unlockpt(fd: c_int) -> c_int {
    let unlock: c_int = 0;
    ioctl(fd, TIOCSPTLCK, &unlock as *const c_int as usize)
}

/// `ptsname_r(3)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ptsname_r(fd: c_int, buf: *mut c_char, len: usize) -> c_int {
    let mut n: c_uint = 0;
    if ioctl(fd, TIOCGPTN, &mut n as *mut c_uint as usize) < 0 {
        return Errno::get().0;
    }
    // Format into a local first: a truncated name would be a different
    // (and possibly existing) device.
    let mut name = [0u8; 32];
    let mut w = crate::fmt::SliceWriter::new(&mut name);
    let _ = core::fmt::write(&mut w, format_args!("/dev/pts/{n}"));
    let written = w.len();
    if written + 1 > len {
        return Errno::ERANGE.0;
    }
    // SAFETY: caller contract; `written + 1 <= len`.
    unsafe {
        core::ptr::copy_nonoverlapping(name.as_ptr(), buf as *mut u8, written);
        *buf.add(written) = 0;
    }
    0
}

/// `ptsname(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ptsname(fd: c_int) -> *mut c_char {
    // SAFETY: the TCB is valid for the life of the thread.
    let buf = unsafe { &mut (*crate::thread::current()).path_buf };
    // SAFETY: the buffer is valid.
    let r = unsafe { ptsname_r(fd, buf.as_mut_ptr() as *mut c_char, buf.len()) };
    if r != 0 {
        Errno(r).set();
        return core::ptr::null_mut();
    }
    buf.as_mut_ptr() as *mut c_char
}
