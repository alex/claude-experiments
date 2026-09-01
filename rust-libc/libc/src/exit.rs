//! Process termination: `exit`, `_exit`, `atexit` and `abort`.

use crate::sync::Mutex;
use crate::sys;
use core::ffi::c_int;

/// Maximum number of `atexit` handlers. C requires at least 32.
const MAX_ATEXIT: usize = 64;

/// A registered exit handler: plain (`atexit`) or with an argument
/// (`__cxa_atexit`).
#[derive(Clone, Copy)]
enum Handler {
    Plain(extern "C" fn()),
    WithArg(
        unsafe extern "C" fn(*mut core::ffi::c_void),
        *mut core::ffi::c_void,
    ),
}
// SAFETY: the raw pointer is only handed back to the function it was
// registered with.
unsafe impl Send for Handler {}

struct AtexitTable {
    handlers: [Option<Handler>; MAX_ATEXIT],
    len: usize,
}

static ATEXIT: Mutex<AtexitTable> = Mutex::new(AtexitTable {
    handlers: [None; MAX_ATEXIT],
    len: 0,
});

fn register(h: Handler) -> c_int {
    let mut table = ATEXIT.lock();
    if table.len == MAX_ATEXIT {
        return -1;
    }
    let len = table.len;
    table.handlers[len] = Some(h);
    table.len += 1;
    0
}

/// Registers a function to be called by [`exit`], in reverse order of
/// registration. Returns non-zero when the table is full.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn atexit(func: extern "C" fn()) -> c_int {
    register(Handler::Plain(func))
}

/// Registers `func(arg)` (for `__cxa_atexit`).
pub fn register_with_arg(
    func: unsafe extern "C" fn(*mut core::ffi::c_void),
    arg: *mut core::ffi::c_void,
) -> c_int {
    register(Handler::WithArg(func, arg))
}

/// Runs the registered `atexit` handlers (last registered first).
/// Handlers registered while running are picked up too, as C requires.
pub fn run_atexit() {
    loop {
        let handler = {
            let mut table = ATEXIT.lock();
            if table.len == 0 {
                return;
            }
            table.len -= 1;
            let len = table.len;
            table.handlers[len].take()
        };
        match handler {
            Some(Handler::Plain(h)) => h(),
            // SAFETY: registered by __cxa_atexit with this argument.
            Some(Handler::WithArg(h, arg)) => unsafe { h(arg) },
            None => {}
        }
    }
}

#[cfg(not(test))]
unsafe extern "C" {
    static __fini_array_start: [Option<unsafe extern "C" fn()>; 0];
    static __fini_array_end: [Option<unsafe extern "C" fn()>; 0];
}

/// Runs the ELF destructors (`.fini_array`, in reverse order).
#[cfg(not(test))]
fn run_fini_array() {
    // SAFETY: the linker guarantees the symbols bracket the array.
    unsafe {
        let start = __fini_array_start.as_ptr();
        let mut p = __fini_array_end.as_ptr();
        while p > start {
            p = p.sub(1);
            if let Some(f) = *p {
                f();
            }
        }
    }
}

#[cfg(test)]
fn run_fini_array() {}

/// The C `exit` function: runs `atexit` handlers and destructors, flushes
/// stdio and terminates the process.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn exit(status: c_int) -> ! {
    run_atexit();
    run_fini_array();
    crate::stdio::flush_all();
    sys::exit_group(status)
}

/// The C `_exit` function: terminates immediately.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn _exit(status: c_int) -> ! {
    sys::exit_group(status)
}

/// The C `_Exit` function (identical to `_exit`).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn _Exit(status: c_int) -> ! {
    sys::exit_group(status)
}

/// The C `abort` function: raises `SIGABRT`, and if that somehow returns
/// (a handler caught it), makes sure the process still dies.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn abort() -> ! {
    abort_now()
}

/// Called by code compiled with `-fstack-protector` when a stack canary
/// has been overwritten.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __stack_chk_fail() -> ! {
    let _ = sys::write_all(2, b"*** stack smashing detected ***: terminated\n");
    abort_now()
}

/// Terminates the process with `SIGABRT`.
pub fn abort_now() -> ! {
    let pid = sys::getpid();
    let tid = sys::gettid();
    // Unblock SIGABRT so the default action (core dump) can happen.
    let mask: u64 = 1 << (sys::SIGABRT - 1);
    // SAFETY: `mask` is a valid signal set.
    let _ = unsafe { sys::rt_sigprocmask(sys::SIG_UNBLOCK, &mask, core::ptr::null_mut()) };
    let _ = sys::tgkill(pid, tid, sys::SIGABRT);
    // A handler returned or SIGABRT is ignored: exit no matter what.
    sys::exit_group(127)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static ORDER: AtomicUsize = AtomicUsize::new(0);
    extern "C" fn first() {
        // Runs last: must see that `second` already ran.
        assert_eq!(ORDER.fetch_add(1, Ordering::SeqCst), 1);
    }
    extern "C" fn second() {
        assert_eq!(ORDER.fetch_add(1, Ordering::SeqCst), 0);
        // Registering during exit is allowed and runs before older handlers.
        assert_eq!(atexit(third), 0);
    }
    extern "C" fn third() {
        // Runs right after `second`, before `first`. Adjust the counter so
        // `first` still sees 1.
        assert_eq!(ORDER.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn atexit_lifo_and_reentrant() {
        assert_eq!(atexit(first), 0);
        assert_eq!(atexit(second), 0);
        run_atexit();
        assert_eq!(ORDER.load(Ordering::SeqCst), 2);
        assert_eq!(ATEXIT.lock().len, 0);
    }
}
