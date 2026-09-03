//! `<time.h>` and `<sys/time.h>`.
//!
//! Clocks go straight to the kernel (no vDSO yet). Calendar conversion
//! implements the proleptic Gregorian calendar with the well known
//! days-from-civil algorithm. Time zones (`TZ`, TZif files, POSIX rules)
//! live in `tz.rs`.

pub mod calendar;
pub mod strftime;
pub mod tz;

use crate::c_char;
use crate::errno::{CReturn, Errno};
use crate::sys::{self, Timespec};
use core::ffi::{c_int, c_long, c_uint, c_void};
use core::ptr;

/// `struct tm`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tm {
    /// Seconds `[0, 60]`.
    pub tm_sec: c_int,
    /// Minutes `[0, 59]`.
    pub tm_min: c_int,
    /// Hours `[0, 23]`.
    pub tm_hour: c_int,
    /// Day of month `[1, 31]`.
    pub tm_mday: c_int,
    /// Month `[0, 11]`.
    pub tm_mon: c_int,
    /// Years since 1900.
    pub tm_year: c_int,
    /// Day of week `[0, 6]`, Sunday = 0.
    pub tm_wday: c_int,
    /// Day of year `[0, 365]`.
    pub tm_yday: c_int,
    /// Daylight saving flag.
    pub tm_isdst: c_int,
    /// Offset from UTC in seconds.
    pub tm_gmtoff: c_long,
    /// Time zone abbreviation.
    pub tm_zone: *const c_char,
}

/// `struct timeval`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Timeval {
    /// Seconds.
    pub tv_sec: i64,
    /// Microseconds.
    pub tv_usec: i64,
}

/// `struct timezone` (obsolete).
#[repr(C)]
pub struct TimezoneStruct {
    tz_minuteswest: c_int,
    tz_dsttime: c_int,
}

static UTC: &[u8; 4] = b"UTC\0";

/// `tzname`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut tzname: [*mut c_char; 2] =
    [UTC.as_ptr() as *mut c_char, UTC.as_ptr() as *mut c_char];
/// `timezone`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut timezone: c_long = 0;
/// `daylight`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut daylight: c_int = 0;

/// `clock_gettime(2)`.
///
/// # Safety
/// `ts` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn clock_gettime(clock: c_int, ts: *mut Timespec) -> c_int {
    // Straight into the vDSO with the caller's pointer when there is one.
    // SAFETY: caller contract.
    if let Some(r) = unsafe { crate::vdso::clock_gettime(clock, ts) } {
        if r == 0 {
            return 0;
        }
        Errno(-r).set();
        return -1;
    }
    match sys::clock_gettime(clock) {
        Ok(v) => {
            // SAFETY: caller contract.
            unsafe { *ts = v };
            0
        }
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `clock_getres(2)`.
///
/// # Safety
/// `ts` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn clock_getres(clock: c_int, ts: *mut Timespec) -> c_int {
    // SAFETY: the kernel accepts a null result pointer.
    let r = unsafe {
        crate::arch::syscall2(crate::arch::nr::CLOCK_GETRES, clock as usize, ts as usize)
    };
    sys::check(r).map(drop).c_ret()
}

/// `clock_settime(2)`.
///
/// # Safety
/// `ts` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn clock_settime(clock: c_int, ts: *const Timespec) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall2(crate::arch::nr::CLOCK_SETTIME, clock as usize, ts as usize)
    };
    sys::check(r).map(drop).c_ret()
}

/// `clock_nanosleep(2)`. Returns the error number directly, as POSIX
/// specifies for this function.
///
/// # Safety
/// `req` must be valid; `rem` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn clock_nanosleep(
    clock: c_int,
    flags: c_int,
    req: *const Timespec,
    rem: *mut Timespec,
) -> c_int {
    crate::thread::cancel_point();
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall4(
            crate::arch::nr::CLOCK_NANOSLEEP,
            clock as usize,
            flags as usize,
            req as usize,
            rem as usize,
        )
    };
    match sys::check(r) {
        Ok(_) => 0,
        Err(e) => e.0,
    }
}

/// `nanosleep(2)`.
///
/// # Safety
/// `req` must be valid; `rem` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn nanosleep(req: *const Timespec, rem: *mut Timespec) -> c_int {
    // SAFETY: forwarded.
    let r = unsafe { clock_nanosleep(sys::CLOCK_REALTIME, 0, req, rem) };
    crate::thread::cancel_point();
    if r == 0 {
        0
    } else {
        Errno(r).set();
        -1
    }
}

/// `sleep(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sleep(seconds: c_uint) -> c_uint {
    let req = Timespec {
        tv_sec: seconds as i64,
        tv_nsec: 0,
    };
    let mut rem = Timespec::default();
    // SAFETY: valid pointers.
    if unsafe { nanosleep(&req, &mut rem) } == 0 {
        0
    } else {
        rem.tv_sec as c_uint + (rem.tv_nsec > 0) as c_uint
    }
}

/// `usleep(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn usleep(usec: c_uint) -> c_int {
    let req = Timespec {
        tv_sec: (usec / 1_000_000) as i64,
        tv_nsec: (usec % 1_000_000) as c_long * 1000,
    };
    // SAFETY: valid pointer.
    unsafe { nanosleep(&req, ptr::null_mut()) }
}

/// `time(2)`.
///
/// # Safety
/// `out` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn time(out: *mut i64) -> i64 {
    let now = sys::clock_gettime(sys::CLOCK_REALTIME)
        .map(|t| t.tv_sec)
        .unwrap_or(-1);
    if !out.is_null() {
        // SAFETY: caller contract.
        unsafe { *out = now };
    }
    now
}

/// `gettimeofday(2)`.
///
/// # Safety
/// `tv` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gettimeofday(tv: *mut Timeval, _tz: *mut c_void) -> c_int {
    if tv.is_null() {
        return 0;
    }
    match sys::clock_gettime(sys::CLOCK_REALTIME) {
        Ok(t) => {
            // SAFETY: caller contract.
            unsafe {
                *tv = Timeval {
                    tv_sec: t.tv_sec,
                    tv_usec: t.tv_nsec / 1000,
                }
            };
            0
        }
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `clock(3)`: process CPU time in `CLOCKS_PER_SEC` (microseconds).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn clock() -> c_long {
    match sys::clock_gettime(sys::CLOCK_PROCESS_CPUTIME_ID) {
        Ok(t) => t
            .tv_sec
            .saturating_mul(1_000_000)
            .saturating_add(t.tv_nsec / 1000),
        Err(_) => -1,
    }
}

/// `difftime(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn difftime(a: i64, b: i64) -> f64 {
    a as f64 - b as f64
}

/// `tzset(3)`: loads the zone named by `TZ` and sets `tzname`,
/// `timezone` and `daylight`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tzset() {
    let (std, dst, west, has_dst) = tz::tzset();
    // SAFETY: plain globals, written under the zone lock's protection in
    // practice (concurrent tzset calls store the same values).
    unsafe {
        tzname = [std as *mut c_char, dst as *mut c_char];
        timezone = west as c_long;
        daylight = has_dst as c_int;
    }
}

/// `gmtime_r(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gmtime_r(t: *const i64, out: *mut Tm) -> *mut Tm {
    // SAFETY: caller contract.
    match calendar::to_tm(unsafe { *t }) {
        Some(tm) => {
            // SAFETY: caller contract.
            unsafe { *out = tm };
            out
        }
        None => {
            Errno::EOVERFLOW.set();
            ptr::null_mut()
        }
    }
}

/// `gmtime(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gmtime(t: *const i64) -> *mut Tm {
    // SAFETY: the TCB is valid for the life of the thread.
    let out = unsafe { &raw mut (*crate::thread::current()).tm };
    // SAFETY: forwarded.
    unsafe { gmtime_r(t, out) }
}

/// `localtime_r(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn localtime_r(t: *const i64, out: *mut Tm) -> *mut Tm {
    // SAFETY: caller contract.
    let t = unsafe { *t };
    let info = tz::local(t);
    match t.checked_add(info.gmtoff).and_then(calendar::to_tm) {
        Some(mut tm) => {
            tm.tm_isdst = info.isdst as c_int;
            tm.tm_gmtoff = info.gmtoff as c_long;
            tm.tm_zone = info.zone;
            // SAFETY: caller contract.
            unsafe { *out = tm };
            out
        }
        None => {
            Errno::EOVERFLOW.set();
            ptr::null_mut()
        }
    }
}

/// `localtime(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn localtime(t: *const i64) -> *mut Tm {
    // SAFETY: the TCB is valid for the life of the thread.
    let out = unsafe { &raw mut (*crate::thread::current()).tm };
    // SAFETY: forwarded.
    unsafe { localtime_r(t, out) }
}

/// `timegm(3)`: normalises `tm` and returns the corresponding time.
///
/// # Safety
/// `tm` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn timegm(tm: *mut Tm) -> i64 {
    // SAFETY: caller contract.
    let t = unsafe { &mut *tm };
    match calendar::from_tm(t) {
        Some(secs) => {
            if let Some(norm) = calendar::to_tm(secs) {
                *t = norm;
            }
            secs
        }
        None => {
            Errno::EOVERFLOW.set();
            -1
        }
    }
}

/// `mktime(3)` (UTC).
///
/// # Safety
/// `tm` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mktime(tm: *mut Tm) -> i64 {
    // SAFETY: caller contract.
    let t = unsafe { &mut *tm };
    let Some(local_secs) = calendar::from_tm(t) else {
        Errno::EOVERFLOW.set();
        return -1;
    };
    let isdst = match t.tm_isdst {
        0 => Some(false),
        d if d > 0 => Some(true),
        _ => None,
    };
    let secs = tz::from_local(local_secs, isdst);
    // SAFETY: `tm` is valid.
    if unsafe { localtime_r(&secs, tm) }.is_null() {
        return -1;
    }
    secs
}

/// `asctime_r(3)`: `buf` must hold at least 26 bytes.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn asctime_r(tm: *const Tm, buf: *mut c_char) -> *mut c_char {
    // SAFETY: caller contract.
    let tm = unsafe { &*tm };
    let (Some(wday), Some(mon)) = (
        calendar::WDAY_NAMES.get(tm.tm_wday as usize),
        calendar::MON_NAMES.get(tm.tm_mon as usize),
    ) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    // Format into a local: the fixed 26-byte layout cannot represent a
    // year outside four digits or fields wider than their columns.
    let mut tmp = [0u8; 64];
    let mut w = crate::fmt::SliceWriter::new(&mut tmp);
    let _ = core::fmt::write(
        &mut w,
        format_args!(
            "{wday} {mon} {:2} {:02}:{:02}:{:02} {}\n",
            tm.tm_mday,
            tm.tm_hour,
            tm.tm_min,
            tm.tm_sec,
            tm.tm_year as i64 + 1900
        ),
    );
    let len = w.len();
    if len != 25 {
        Errno::EOVERFLOW.set();
        return ptr::null_mut();
    }
    // SAFETY: the buffer holds 26 bytes.
    unsafe {
        ptr::copy_nonoverlapping(tmp.as_ptr(), buf as *mut u8, len);
        *buf.add(len) = 0;
    }
    buf
}

/// `asctime(3)`.
///
/// # Safety
/// `tm` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn asctime(tm: *const Tm) -> *mut c_char {
    // SAFETY: the TCB is valid for the life of the thread.
    let buf = unsafe { (*crate::thread::current()).asctime_buf.as_mut_ptr() as *mut c_char };
    // SAFETY: forwarded.
    unsafe { asctime_r(tm, buf) }
}

/// `ctime_r(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ctime_r(t: *const i64, buf: *mut c_char) -> *mut c_char {
    let mut tm = Tm::default();
    // SAFETY: forwarded.
    unsafe {
        if localtime_r(t, &mut tm).is_null() {
            return ptr::null_mut();
        }
        asctime_r(&tm, buf)
    }
}

/// `ctime(3)`.
///
/// # Safety
/// `t` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ctime(t: *const i64) -> *mut c_char {
    // SAFETY: forwarded.
    unsafe {
        let tm = localtime(t);
        if tm.is_null() {
            return ptr::null_mut();
        }
        asctime(tm)
    }
}

/// `timespec_get(3)` (C11): only `TIME_UTC` (1) is supported.
///
/// # Safety
/// `ts` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn timespec_get(ts: *mut Timespec, base: c_int) -> c_int {
    if base != 1 {
        return 0;
    }
    // SAFETY: forwarded.
    if unsafe { clock_gettime(sys::CLOCK_REALTIME, ts) } == 0 {
        1
    } else {
        0
    }
}
