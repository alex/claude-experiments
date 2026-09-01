//! `<assert.h>`, `<err.h>` and program name globals.

use crate::c_char;
use crate::stdio::printf::Sink;
use crate::stdio::{lock, stderr};
use core::ffi::c_int;

/// `program_invocation_name` (the full `argv[0]`).
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut program_invocation_name: *mut c_char = c"".as_ptr() as *mut c_char;
/// `program_invocation_short_name` (`argv[0]` after the last slash).
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut program_invocation_short_name: *mut c_char = c"".as_ptr() as *mut c_char;
/// `__progname` (BSD name for the short name).
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut __progname: *mut c_char = c"".as_ptr() as *mut c_char;

/// Records the program name from `argv[0]` at startup.
///
/// # Safety
/// `argv0` must be NUL-terminated and live for the whole process.
pub unsafe fn set_program_name(argv0: *mut c_char) {
    if argv0.is_null() {
        return;
    }
    // SAFETY: caller contract.
    unsafe {
        let len = crate::string::search::strlen(argv0 as *const u8);
        let bytes = core::slice::from_raw_parts(argv0 as *const u8, len);
        let short = match crate::string::search::memrchr(bytes, b'/') {
            Some(i) => argv0.add(i + 1),
            None => argv0,
        };
        program_invocation_name = argv0;
        program_invocation_short_name = short;
        __progname = short;
    }
}

/// `__assert_fail`, called by the `assert` macro.
///
/// # Safety
/// All strings must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __assert_fail(
    expr: *const c_char,
    file: *const c_char,
    line: c_int,
    func: *const c_char,
) -> ! {
    // SAFETY: stderr is always valid.
    let mut g = unsafe { lock(stderr) };
    let mut out = crate::stdio::printf::Staged::new(&mut g);
    let s = |p: *const c_char| -> &[u8] {
        if p.is_null() {
            b"?"
        } else {
            // SAFETY: caller contract.
            unsafe {
                core::slice::from_raw_parts(
                    p as *const u8,
                    crate::string::search::strlen(p as *const u8),
                )
            }
        }
    };
    let mut num = [0u8; 16];
    let mut w = crate::fmt::SliceWriter::new(&mut num);
    let _ = core::fmt::write(&mut w, format_args!("{line}"));
    let n = w.len();
    // SAFETY: the program name is NUL-terminated.
    out.write(s(unsafe { __progname }));
    out.write(b": ");
    out.write(s(file));
    out.write(b":");
    out.write(&num[..n]);
    out.write(b": ");
    out.write(s(func));
    out.write(b": Assertion `");
    out.write(s(expr));
    out.write(b"' failed.\n");
    out.finish();
    drop(g);
    crate::exit::abort_now()
}

/// Shared implementation of the `err`/`warn` family.
///
/// # Safety
/// `fmt` must be null or NUL-terminated with matching arguments.
unsafe fn warn_impl(fmt: *const c_char, ap: *mut crate::arch::va::VaList, with_errno: bool) {
    let err = crate::errno::Errno::get().0;
    // SAFETY: stderr is always valid.
    let mut g = unsafe { lock(stderr) };
    let mut out = crate::stdio::printf::Staged::new(&mut g);
    // SAFETY: the program name is NUL-terminated.
    let name = unsafe { __progname };
    // SAFETY: as above.
    out.write(unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    });
    out.write(b": ");
    if !fmt.is_null() {
        // SAFETY: caller contract.
        unsafe { crate::stdio::printf::format(&mut out, fmt as *const u8, &mut *ap) };
        if with_errno {
            out.write(b": ");
        }
    }
    if with_errno {
        let msg = crate::string::str::strerror(err);
        // SAFETY: strerror returns NUL-terminated strings.
        out.write(unsafe {
            core::slice::from_raw_parts(
                msg as *const u8,
                crate::string::search::strlen(msg as *const u8),
            )
        });
    }
    out.write(b"\n");
    out.finish();
}

/// `vwarn(3)`.
///
/// # Safety
/// As for `vfprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vwarn(fmt: *const c_char, ap: *mut crate::arch::va::VaList) {
    // SAFETY: forwarded.
    unsafe { warn_impl(fmt, ap, true) }
}

/// `vwarnx(3)`.
///
/// # Safety
/// As for `vfprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vwarnx(fmt: *const c_char, ap: *mut crate::arch::va::VaList) {
    // SAFETY: forwarded.
    unsafe { warn_impl(fmt, ap, false) }
}

/// `verr(3)`.
///
/// # Safety
/// As for `vfprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn verr(
    status: c_int,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> ! {
    // SAFETY: forwarded.
    unsafe { warn_impl(fmt, ap, true) };
    crate::exit::exit(status)
}

/// `verrx(3)`.
///
/// # Safety
/// As for `vfprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn verrx(
    status: c_int,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> ! {
    // SAFETY: forwarded.
    unsafe { warn_impl(fmt, ap, false) };
    crate::exit::exit(status)
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(warn, 1, "rsi", super::vwarn);
    variadic_stub!(warnx, 1, "rsi", super::vwarnx);
    variadic_stub!(err, 2, "rdx", super::verr);
    variadic_stub!(errx, 2, "rdx", super::verrx);
}
