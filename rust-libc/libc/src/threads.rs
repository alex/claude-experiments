//! C11 `<threads.h>`, layered on the pthread implementation.

use crate::malloc;
use crate::sys::Timespec;
use crate::thread::pthread::{self, PthreadT};
use crate::thread::sync::{self as psync, Cond, Mutex, MutexAttr};
use core::ffi::{c_int, c_void};
use core::sync::atomic::AtomicU32;

/// `thrd_success`.
pub const THRD_SUCCESS: c_int = 0;
/// `thrd_busy`.
pub const THRD_BUSY: c_int = 1;
/// `thrd_error`.
pub const THRD_ERROR: c_int = 2;
/// `thrd_nomem`.
pub const THRD_NOMEM: c_int = 3;
/// `thrd_timedout`.
pub const THRD_TIMEDOUT: c_int = 4;

/// Maps a pthread error number to a `thrd_*` status.
fn status(r: c_int) -> c_int {
    match r {
        0 => THRD_SUCCESS,
        16 => THRD_BUSY,       // EBUSY
        12 | 11 => THRD_NOMEM, // ENOMEM, EAGAIN
        110 => THRD_TIMEDOUT,  // ETIMEDOUT
        _ => THRD_ERROR,
    }
}

type ThrdStart = unsafe extern "C" fn(*mut c_void) -> c_int;

#[repr(C)]
struct StartArgs {
    func: ThrdStart,
    arg: *mut c_void,
}

unsafe extern "C" fn trampoline(p: *mut c_void) -> *mut c_void {
    // SAFETY: `p` is the StartArgs block allocated in thrd_create.
    let (func, arg) = unsafe {
        let a = &*(p as *const StartArgs);
        (a.func, a.arg)
    };
    // SAFETY: our own block.
    unsafe { malloc::dealloc(p as *mut u8) };
    // SAFETY: caller contract of thrd_create.
    let r = unsafe { func(arg) };
    r as isize as *mut c_void
}

/// `thrd_create(3)`.
///
/// # Safety
/// `thr` must be valid; `func` a valid function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn thrd_create(
    thr: *mut PthreadT,
    func: ThrdStart,
    arg: *mut c_void,
) -> c_int {
    let args = malloc::alloc(core::mem::size_of::<StartArgs>()) as *mut StartArgs;
    if args.is_null() {
        return THRD_NOMEM;
    }
    // SAFETY: fresh block.
    unsafe { args.write(StartArgs { func, arg }) };
    // SAFETY: forwarded.
    let r =
        unsafe { pthread::pthread_create(thr, core::ptr::null(), trampoline, args as *mut c_void) };
    if r != 0 {
        // SAFETY: the thread was not created.
        unsafe { malloc::dealloc(args as *mut u8) };
    }
    status(r)
}

/// `thrd_join(3)`.
///
/// # Safety
/// `res` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn thrd_join(thr: PthreadT, res: *mut c_int) -> c_int {
    let mut out: *mut c_void = core::ptr::null_mut();
    // SAFETY: forwarded.
    let r = unsafe { pthread::pthread_join(thr, &mut out) };
    if r == 0 && !res.is_null() {
        // SAFETY: caller contract.
        unsafe { *res = out as isize as c_int };
    }
    status(r)
}

/// `thrd_detach(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn thrd_detach(thr: PthreadT) -> c_int {
    // SAFETY: a thread handle.
    status(unsafe { pthread::pthread_detach(thr) })
}

/// `thrd_current(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn thrd_current() -> PthreadT {
    pthread::pthread_self()
}

/// `thrd_equal(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn thrd_equal(a: PthreadT, b: PthreadT) -> c_int {
    (a == b) as c_int
}

/// `thrd_exit(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn thrd_exit(res: c_int) -> ! {
    pthread::pthread_exit(res as isize as *mut c_void)
}

/// `thrd_yield(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn thrd_yield() {
    crate::sys::sched_yield();
}

/// `thrd_sleep(3)`: 0 on success, -1 if interrupted, -2 on other errors.
///
/// # Safety
/// `req` must be valid; `rem` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn thrd_sleep(req: *const Timespec, rem: *mut Timespec) -> c_int {
    // SAFETY: forwarded.
    match unsafe { crate::time::clock_nanosleep(crate::sys::CLOCK_REALTIME, 0, req, rem) } {
        0 => 0,
        4 => -1, // EINTR
        _ => -2,
    }
}

/// `mtx_init(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mtx_init(m: *mut Mutex, kind: c_int) -> c_int {
    const MTX_RECURSIVE: c_int = 2;
    let mut attr = core::mem::MaybeUninit::<MutexAttr>::uninit();
    // SAFETY: valid storage; forwarded.
    unsafe {
        psync::pthread_mutexattr_init(attr.as_mut_ptr());
        if kind & MTX_RECURSIVE != 0 {
            psync::pthread_mutexattr_settype(attr.as_mut_ptr(), 1);
        }
        status(psync::pthread_mutex_init(m, attr.as_ptr()))
    }
}

/// `mtx_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn mtx_destroy(_m: *mut Mutex) {}

/// `mtx_lock(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mtx_lock(m: *mut Mutex) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_mutex_lock(m) })
}

/// `mtx_trylock(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mtx_trylock(m: *mut Mutex) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_mutex_trylock(m) })
}

/// `mtx_timedlock(3)`.
///
/// # Safety
/// `m` and `deadline` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mtx_timedlock(m: *mut Mutex, deadline: *const Timespec) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_mutex_timedlock(m, deadline) })
}

/// `mtx_unlock(3)`.
///
/// # Safety
/// `m` must be valid and held.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mtx_unlock(m: *mut Mutex) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_mutex_unlock(m) })
}

/// `cnd_init(3)`.
///
/// # Safety
/// `c` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cnd_init(c: *mut Cond) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_cond_init(c, core::ptr::null()) })
}

/// `cnd_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn cnd_destroy(_c: *mut Cond) {}

/// `cnd_signal(3)`.
///
/// # Safety
/// `c` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cnd_signal(c: *mut Cond) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_cond_signal(c) })
}

/// `cnd_broadcast(3)`.
///
/// # Safety
/// `c` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cnd_broadcast(c: *mut Cond) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_cond_broadcast(c) })
}

/// `cnd_wait(3)`.
///
/// # Safety
/// `c` and `m` must be valid; `m` held.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cnd_wait(c: *mut Cond, m: *mut Mutex) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_cond_wait(c, m) })
}

/// `cnd_timedwait(3)`.
///
/// # Safety
/// As for [`cnd_wait`]; `deadline` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn cnd_timedwait(
    c: *mut Cond,
    m: *mut Mutex,
    deadline: *const Timespec,
) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { psync::pthread_cond_timedwait(c, m, deadline) })
}

/// `tss_create(3)`.
///
/// # Safety
/// `key` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tss_create(
    key: *mut c_int,
    dtor: Option<unsafe extern "C" fn(*mut c_void)>,
) -> c_int {
    // SAFETY: forwarded.
    status(unsafe { pthread::pthread_key_create(key, dtor) })
}

/// `tss_delete(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tss_delete(key: c_int) {
    pthread::pthread_key_delete(key);
}

/// `tss_get(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tss_get(key: c_int) -> *mut c_void {
    pthread::pthread_getspecific(key)
}

/// `tss_set(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tss_set(key: c_int, value: *mut c_void) -> c_int {
    status(pthread::pthread_setspecific(key, value))
}

/// `call_once(3)`.
///
/// # Safety
/// `flag` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn call_once(flag: *mut AtomicU32, func: extern "C" fn()) {
    // SAFETY: forwarded.
    unsafe { psync::pthread_once(flag, func) };
}
