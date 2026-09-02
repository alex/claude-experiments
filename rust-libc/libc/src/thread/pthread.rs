//! `pthread_create`, `join`, `detach`, `exit`, attributes, keys and
//! the `atfork` registry.
//!
//! A `pthread_t` is the address of the thread's [`Tcb`]. Each thread gets
//! one mapping holding, from the bottom: a guard page, the stack, and the
//! static TLS block with the TCB at the top:
//!
//! ```text
//!  map_base                                                map_base+map_len
//!  | guard (PROT_NONE) |  stack (grows down)  | TLS block | Tcb |
//! ```
//!
//! Joining waits on the `tid` word, which the kernel clears (and wakes)
//! when the thread exits thanks to `CLONE_CHILD_CLEARTID`. The stack
//! mapping is released by whoever is last: the joiner, or the exiting
//! thread itself when detached (which has to unmap its own stack from
//! assembly, see `arch`).
//!
//! Cancellation (`pthread_cancel`) is not implemented.

use super::{
    CleanupRecord, KEYS_MAX, STATE_DETACHED, STATE_EXITED, STATE_JOINABLE, Tcb, current, tls,
};
use crate::errno::Errno;
use crate::sync::Mutex;
use crate::sys::{
    self, MAP_ANONYMOUS, MAP_NORESERVE, MAP_PRIVATE, MAP_STACK, PAGE_SIZE, PROT_NONE, PROT_READ,
    PROT_WRITE,
};
use core::ffi::{c_int, c_void};
use core::ptr;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

/// `pthread_t`.
pub type PthreadT = usize;

/// Default stack size for new threads.
const DEFAULT_STACK: usize = 8 << 20;
/// Default guard size.
const DEFAULT_GUARD: usize = PAGE_SIZE;

/// `pthread_attr_t`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Attr {
    stack_size: usize,
    guard_size: usize,
    stack_addr: *mut c_void,
    detached: c_int,
    _pad: c_int,
}

/// Number of live threads; the last one to exit ends the process.
static THREADS: AtomicUsize = AtomicUsize::new(1);

/// Entry point of every new thread, running on its own stack.
extern "C" fn thread_start(arg: *mut c_void) -> c_int {
    let tcb = arg as *mut Tcb;
    // SAFETY: the TCB was fully initialised by pthread_create and the
    // thread pointer was set by the kernel (CLONE_SETTLS).
    let result = unsafe {
        let start = (*tcb).start.expect("thread start routine");
        start((*tcb).arg)
    };
    exit_thread(result)
}

/// Mappings of joined threads, kept for reuse: creating a thread then
/// costs a `clone` rather than `mmap`, `mprotect`, page faults and
/// `munmap` as well. Only exact size matches are reused (almost every
/// thread uses the default stack size), and the guard page is already in
/// place. Detached threads still unmap their own stack on exit.
struct StackCache {
    /// `(base, length, guard)`.
    entries: [(usize, usize, usize); STACK_CACHE_SLOTS],
    count: usize,
}

const STACK_CACHE_SLOTS: usize = 8;

static STACK_CACHE: crate::sync::Mutex<StackCache> = crate::sync::Mutex::new(StackCache {
    entries: [(0, 0, 0); STACK_CACHE_SLOTS],
    count: 0,
});

/// Takes a cached mapping of exactly `len` bytes with a `guard`-byte guard.
fn take_stack(len: usize, guard: usize) -> Option<*mut u8> {
    let mut cache = STACK_CACHE.lock();
    let i = (0..cache.count).find(|&i| cache.entries[i].1 == len && cache.entries[i].2 == guard)?;
    let base = cache.entries[i].0;
    cache.count -= 1;
    cache.entries[i] = cache.entries[cache.count];
    Some(base as *mut u8)
}

/// Caches or unmaps the mapping of a finished thread.
///
/// # Safety
/// The mapping must be ours and no longer in use.
unsafe fn release_stack(base: *mut u8, len: usize, guard: usize) {
    {
        let mut cache = STACK_CACHE.lock();
        if cache.count < STACK_CACHE_SLOTS {
            let n = cache.count;
            cache.entries[n] = (base as usize, len, guard);
            cache.count = n + 1;
            return;
        }
    }
    // SAFETY: caller contract.
    let _ = unsafe { sys::munmap(base, len) };
}

/// Locks the thread-global state for `fork`.
pub fn prefork() {
    STACK_CACHE.raw().lock();
}

/// Unlocks the state taken by [`prefork`].
///
/// # Safety
/// Must follow a call to [`prefork`] on the same thread.
pub unsafe fn postfork() {
    // SAFETY: caller contract.
    unsafe { STACK_CACHE.raw().unlock() };
}

/// `pthread_create(3)`.
///
/// # Safety
/// `out` must be valid; `attr` null or valid; `start` a valid function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_create(
    out: *mut PthreadT,
    attr: *const Attr,
    start: unsafe extern "C" fn(*mut c_void) -> *mut c_void,
    arg: *mut c_void,
) -> c_int {
    // SAFETY: caller contract.
    let attr = unsafe { attr.as_ref().copied() }.unwrap_or(DEFAULT_ATTR);
    let tls_len = tls::round_up(tls::region_size(), 16);
    let guard = tls::round_up(attr.guard_size, PAGE_SIZE);
    let stack = tls::round_up(attr.stack_size.max(16 * 1024), PAGE_SIZE);
    let Some(len) = guard
        .checked_add(stack)
        .and_then(|v| v.checked_add(tls_len))
        .map(|v| tls::round_up(v, PAGE_SIZE))
    else {
        return Errno::EINVAL.0;
    };
    let base = match take_stack(len, guard) {
        Some(base) => base,
        None => {
            // SAFETY: fresh anonymous mapping.
            let base = match unsafe {
                sys::mmap(
                    ptr::null_mut(),
                    len,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_STACK,
                    -1,
                    0,
                )
            } {
                Ok(p) => p,
                Err(e) => return e.0,
            };
            // SAFETY: the guard is part of our fresh mapping.
            if guard > 0 && unsafe { sys::mprotect(base, guard, PROT_NONE) }.is_err() {
                // SAFETY: our mapping.
                let _ = unsafe { sys::munmap(base, len) };
                return Errno::EAGAIN.0;
            }
            base
        }
    };
    // SAFETY: the current TCB is valid.
    let canary = unsafe { (*current()).stack_guard };
    // SAFETY: the TLS region is inside the mapping.
    let tcb = unsafe { tls::install(base.add(len - tls_len), tls_len, canary) };
    // SAFETY: `tcb` was just initialised and is not yet shared.
    unsafe {
        (*tcb).map_base = base;
        (*tcb).map_len = len;
        (*tcb).map_guard = guard;
        (*tcb).state.store(
            if attr.detached != 0 {
                STATE_DETACHED
            } else {
                STATE_JOINABLE
            },
            Ordering::Relaxed,
        );
        (*tcb).start = Some(start);
        (*tcb).arg = arg;
    }
    super::set_threaded();
    THREADS.fetch_add(1, Ordering::Relaxed);
    let flags = sys::CLONE_VM
        | sys::CLONE_FS
        | sys::CLONE_FILES
        | sys::CLONE_SIGHAND
        | sys::CLONE_THREAD
        | sys::CLONE_SYSVSEM
        | sys::CLONE_SETTLS
        | sys::CLONE_PARENT_SETTID
        | sys::CLONE_CHILD_CLEARTID;
    // The stack runs from the guard page up to the TLS region.
    let child_stack = ((base as usize + len - tls_len) & !15) as *mut u8;
    // SAFETY: the stack and TCB are prepared; the tid word lives in the TCB.
    let r = unsafe {
        let tid = (*tcb).tid.as_ptr();
        clone_thread(
            thread_start,
            child_stack,
            flags,
            tcb as *mut c_void,
            tid,
            tcb as *mut u8,
            tid,
        )
    };
    match r {
        Ok(_) => {
            // SAFETY: caller contract.
            unsafe { *out = tcb as PthreadT };
            0
        }
        Err(e) => {
            THREADS.fetch_sub(1, Ordering::Relaxed);
            // SAFETY: the thread was never created; the mapping is ours.
            unsafe { release_stack(base, len, guard) };
            if e == Errno::ENOMEM {
                Errno::EAGAIN.0
            } else {
                e.0
            }
        }
    }
}

#[cfg(not(test))]
use crate::arch::clone_thread;

/// Host tests cannot create real threads with our TCB layout.
#[cfg(test)]
unsafe fn clone_thread(
    _entry: extern "C" fn(*mut c_void) -> c_int,
    _stack: *mut u8,
    _flags: usize,
    _arg: *mut c_void,
    _ptid: *mut u32,
    _tls: *mut u8,
    _ctid: *mut u32,
) -> sys::Result<u32> {
    Err(Errno::ENOSYS)
}

/// Runs the cleanup handlers and key destructors, then terminates the
/// calling thread.
fn exit_thread(result: *mut c_void) -> ! {
    let tcb = current();
    // SAFETY: the TCB is valid and only this thread touches these fields.
    unsafe {
        (*tcb).result = result;
        // Cleanup handlers, innermost first.
        while !(*tcb).cleanup.is_null() {
            let rec = (*tcb).cleanup;
            (*tcb).cleanup = (*rec).next;
            if let Some(f) = (*rec).func {
                f((*rec).arg);
            }
        }
        crate::dl::run_thread_dtors();
        run_key_destructors(tcb);
        // The last thread ends the process as if by exit(0).
        if THREADS.fetch_sub(1, Ordering::AcqRel) == 1 {
            crate::exit::exit(0);
        }
        crate::malloc::abandon(&raw mut (*tcb).heap);
        if (*tcb).map_base.is_null() {
            // The main thread has no mapping of ours to release.
            sys::exit_thread(0);
        }
        // Joinable threads leave the mapping to the joiner. Detached
        // threads (including ones detached after this point, which see
        // STATE_EXITED) must release it themselves.
        if (*tcb)
            .state
            .compare_exchange(
                STATE_JOINABLE,
                STATE_EXITED,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
        {
            sys::exit_thread(0);
        }
        unmap_self((*tcb).map_base, (*tcb).map_len)
    }
}

#[cfg(not(test))]
unsafe fn unmap_self(base: *mut u8, len: usize) -> ! {
    // SAFETY: forwarded.
    unsafe { crate::arch::unmap_self_and_exit(base, len) }
}

#[cfg(test)]
unsafe fn unmap_self(_base: *mut u8, _len: usize) -> ! {
    sys::exit_thread(0)
}

/// `pthread_exit(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_exit(result: *mut c_void) -> ! {
    exit_thread(result)
}

/// Waits for `tcb`'s kernel thread to be gone.
///
/// # Safety
/// `tcb` must be a live TCB.
unsafe fn wait_for_exit(tcb: *mut Tcb) {
    // SAFETY: caller contract.
    let tid = unsafe { &(*tcb).tid };
    loop {
        let t = tid.load(Ordering::Acquire);
        if t == 0 {
            return;
        }
        // The kernel's CLEARTID wake uses a shared key; so must the wait.
        let _ = sys::futex_wait_shared(tid, t);
    }
}

/// `pthread_join(3)`.
///
/// # Safety
/// `thread` must be a joinable thread; `result` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_join(thread: PthreadT, result: *mut *mut c_void) -> c_int {
    let tcb = thread as *mut Tcb;
    if tcb == current() {
        return Errno::EDEADLK.0;
    }
    // SAFETY: caller contract.
    unsafe {
        if (*tcb).state.load(Ordering::Acquire) == STATE_DETACHED {
            return Errno::EINVAL.0;
        }
        wait_for_exit(tcb);
        if !result.is_null() {
            *result = (*tcb).result;
        }
        release_stack((*tcb).map_base, (*tcb).map_len, (*tcb).map_guard);
    }
    0
}

/// `pthread_tryjoin_np(3)`.
///
/// # Safety
/// As for [`pthread_join`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_tryjoin_np(thread: PthreadT, result: *mut *mut c_void) -> c_int {
    let tcb = thread as *mut Tcb;
    // SAFETY: caller contract.
    if unsafe { (*tcb).tid.load(Ordering::Acquire) } != 0 {
        return Errno::EBUSY.0;
    }
    // SAFETY: forwarded.
    unsafe { pthread_join(thread, result) }
}

/// `pthread_detach(3)`.
///
/// # Safety
/// `thread` must be a valid, not yet joined thread.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_detach(thread: PthreadT) -> c_int {
    let tcb = thread as *mut Tcb;
    // SAFETY: caller contract.
    unsafe {
        match (*tcb).state.compare_exchange(
            STATE_JOINABLE,
            STATE_DETACHED,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => 0,
            Err(STATE_EXITED) => {
                // Already finished: reclaim like a join would.
                wait_for_exit(tcb);
                release_stack((*tcb).map_base, (*tcb).map_len, (*tcb).map_guard);
                0
            }
            Err(_) => Errno::EINVAL.0,
        }
    }
}

/// `pthread_self(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_self() -> PthreadT {
    current() as PthreadT
}

/// `pthread_equal(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_equal(a: PthreadT, b: PthreadT) -> c_int {
    (a == b) as c_int
}

/// `pthread_yield` / `sched_yield`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sched_yield() -> c_int {
    sys::sched_yield();
    0
}

/// `pthread_sigmask(3)`.
///
/// # Safety
/// `set` and `old` must be null or valid `sigset_t` pointers.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_sigmask(how: c_int, set: *const u64, old: *mut u64) -> c_int {
    // SAFETY: forwarded.
    match unsafe { sys::rt_sigprocmask(how, set, old) } {
        Ok(()) => 0,
        Err(e) => e.0,
    }
}

/// `pthread_kill(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_kill(thread: PthreadT, sig: c_int) -> c_int {
    let tcb = thread as *mut Tcb;
    // SAFETY: a valid thread handle.
    let tid = unsafe { (*tcb).tid.load(Ordering::Acquire) };
    if tid == 0 {
        return Errno::ESRCH.0;
    }
    match sys::tgkill(sys::getpid(), tid as c_int, sig) {
        Ok(()) => 0,
        Err(e) => e.0,
    }
}

/// `pthread_setname_np(3)` (calling thread only).
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_setname_np(thread: PthreadT, name: *const crate::c_char) -> c_int {
    if thread != pthread_self() {
        return Errno::ENOSYS.0;
    }
    const PR_SET_NAME: usize = 15;
    // SAFETY: caller contract; the kernel copies at most 16 bytes.
    let r = unsafe { crate::arch::syscall2(crate::arch::nr::PRCTL, PR_SET_NAME, name as usize) };
    match sys::check(r) {
        Ok(_) => 0,
        Err(e) => e.0,
    }
}

// ---------------------------------------------------------------------
// Cleanup handlers.

/// `_pthread_cleanup_push` (used by the `pthread_cleanup_push` macro).
///
/// # Safety
/// `rec` must live until the matching pop.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn _pthread_cleanup_push(
    rec: *mut CleanupRecord,
    func: unsafe extern "C" fn(*mut c_void),
    arg: *mut c_void,
) {
    let tcb = current();
    // SAFETY: caller contract.
    unsafe {
        (*rec).func = Some(func);
        (*rec).arg = arg;
        (*rec).next = (*tcb).cleanup;
        (*tcb).cleanup = rec;
    }
}

/// `_pthread_cleanup_pop` (used by the `pthread_cleanup_pop` macro).
///
/// # Safety
/// `rec` must be the innermost pushed record.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn _pthread_cleanup_pop(rec: *mut CleanupRecord, run: c_int) {
    let tcb = current();
    // SAFETY: caller contract.
    unsafe {
        (*tcb).cleanup = (*rec).next;
        if run != 0
            && let Some(f) = (*rec).func
        {
            f((*rec).arg);
        }
    }
}

// ---------------------------------------------------------------------
// Attributes.

const DEFAULT_ATTR: Attr = Attr {
    stack_size: DEFAULT_STACK,
    guard_size: DEFAULT_GUARD,
    stack_addr: ptr::null_mut(),
    detached: 0,
    _pad: 0,
};

/// `pthread_attr_init(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_init(attr: *mut Attr) -> c_int {
    // SAFETY: caller contract.
    unsafe { *attr = DEFAULT_ATTR };
    0
}

/// `pthread_attr_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_attr_destroy(_attr: *mut Attr) -> c_int {
    0
}

/// `pthread_attr_setdetachstate(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_setdetachstate(attr: *mut Attr, state: c_int) -> c_int {
    if !matches!(state, 0 | 1) {
        return Errno::EINVAL.0;
    }
    // SAFETY: caller contract.
    unsafe { (*attr).detached = state };
    0
}

/// `pthread_attr_getdetachstate(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_getdetachstate(
    attr: *const Attr,
    state: *mut c_int,
) -> c_int {
    // SAFETY: caller contract.
    unsafe { *state = (*attr).detached };
    0
}

/// `pthread_attr_setstacksize(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_setstacksize(attr: *mut Attr, size: usize) -> c_int {
    if size < 16 * 1024 {
        return Errno::EINVAL.0;
    }
    // SAFETY: caller contract.
    unsafe { (*attr).stack_size = size };
    0
}

/// `pthread_attr_getstacksize(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_getstacksize(attr: *const Attr, size: *mut usize) -> c_int {
    // SAFETY: caller contract.
    unsafe { *size = (*attr).stack_size };
    0
}

/// `pthread_attr_setguardsize(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_setguardsize(attr: *mut Attr, size: usize) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*attr).guard_size = size };
    0
}

/// `pthread_attr_getguardsize(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_attr_getguardsize(attr: *const Attr, size: *mut usize) -> c_int {
    // SAFETY: caller contract.
    unsafe { *size = (*attr).guard_size };
    0
}

// ---------------------------------------------------------------------
// Thread-specific data.

/// Registry of keys: a destructor pointer per key, with `KEY_FREE` /
/// `KEY_NO_DTOR` sentinels.
static KEYS: [AtomicPtr<c_void>; KEYS_MAX] = [const { AtomicPtr::new(KEY_FREE) }; KEYS_MAX];
const KEY_FREE: *mut c_void = ptr::null_mut();
const KEY_NO_DTOR: *mut c_void = ptr::without_provenance_mut(1);
static KEY_LOCK: Mutex<()> = Mutex::new(());

/// `pthread_key_create(3)`.
///
/// # Safety
/// `key` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_key_create(
    key: *mut c_int,
    dtor: Option<unsafe extern "C" fn(*mut c_void)>,
) -> c_int {
    let _guard = KEY_LOCK.lock();
    let value = match dtor {
        Some(f) => f as *mut c_void,
        None => KEY_NO_DTOR,
    };
    for (i, slot) in KEYS.iter().enumerate() {
        if slot.load(Ordering::Relaxed) == KEY_FREE {
            slot.store(value, Ordering::Release);
            // SAFETY: caller contract.
            unsafe { *key = i as c_int };
            return 0;
        }
    }
    Errno::EAGAIN.0
}

/// `pthread_key_delete(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_key_delete(key: c_int) -> c_int {
    let _guard = KEY_LOCK.lock();
    match KEYS.get(key as usize) {
        Some(slot) if slot.load(Ordering::Relaxed) != KEY_FREE => {
            slot.store(KEY_FREE, Ordering::Release);
            0
        }
        _ => Errno::EINVAL.0,
    }
}

/// `pthread_getspecific(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_getspecific(key: c_int) -> *mut c_void {
    if key < 0 || key as usize >= KEYS_MAX {
        return ptr::null_mut();
    }
    // SAFETY: the TCB is valid.
    unsafe { (*current()).keys[key as usize] }
}

/// `pthread_setspecific(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_setspecific(key: c_int, value: *const c_void) -> c_int {
    if key < 0 || key as usize >= KEYS_MAX || KEYS[key as usize].load(Ordering::Relaxed) == KEY_FREE
    {
        return Errno::EINVAL.0;
    }
    // SAFETY: the TCB is valid.
    unsafe { (*current()).keys[key as usize] = value as *mut c_void };
    0
}

/// Runs key destructors for the exiting thread (at most
/// `PTHREAD_DESTRUCTOR_ITERATIONS` rounds).
///
/// # Safety
/// `tcb` must be the calling thread's TCB.
unsafe fn run_key_destructors(tcb: *mut Tcb) {
    for _ in 0..4 {
        let mut again = false;
        for (i, slot) in KEYS.iter().enumerate() {
            // SAFETY: caller contract.
            let value = unsafe { (*tcb).keys[i] };
            if value.is_null() {
                continue;
            }
            let dtor = slot.load(Ordering::Acquire);
            // SAFETY: caller contract.
            unsafe { (*tcb).keys[i] = ptr::null_mut() };
            if dtor != KEY_FREE && dtor != KEY_NO_DTOR {
                // SAFETY: the slot holds a destructor function pointer.
                let f: unsafe extern "C" fn(*mut c_void) = unsafe { core::mem::transmute(dtor) };
                // SAFETY: the value belongs to this key.
                unsafe { f(value) };
                again = true;
            }
        }
        if !again {
            break;
        }
    }
}

// ---------------------------------------------------------------------
// atfork.

/// Handlers registered with `pthread_atfork`.
pub struct AtforkHandlers {
    /// (prepare, parent, child) triples.
    entries: [(
        Option<extern "C" fn()>,
        Option<extern "C" fn()>,
        Option<extern "C" fn()>,
    ); MAX_ATFORK],
    len: usize,
}
const MAX_ATFORK: usize = 32;

/// The registry, used by `fork`.
pub static ATFORK: Mutex<AtforkHandlers> = Mutex::new(AtforkHandlers {
    entries: [(None, None, None); MAX_ATFORK],
    len: 0,
});

impl AtforkHandlers {
    /// Runs the prepare handlers (in reverse registration order).
    pub fn run_prepare(&self) {
        for i in (0..self.len).rev() {
            if let Some(f) = self.entries[i].0 {
                f();
            }
        }
    }

    /// Runs the parent (`child == false`) or child handlers.
    pub fn run_after(&self, child: bool) {
        for i in 0..self.len {
            let f = if child {
                self.entries[i].2
            } else {
                self.entries[i].1
            };
            if let Some(f) = f {
                f();
            }
        }
    }
}

/// `pthread_atfork(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_atfork(
    prepare: Option<extern "C" fn()>,
    parent: Option<extern "C" fn()>,
    child: Option<extern "C" fn()>,
) -> c_int {
    let mut reg = ATFORK.lock();
    if reg.len == MAX_ATFORK {
        return Errno::ENOMEM.0;
    }
    let len = reg.len;
    reg.entries[len] = (prepare, parent, child);
    reg.len += 1;
    0
}

/// Resets the thread bookkeeping in a forked child (single thread).
pub fn after_fork_in_child() {
    THREADS.store(1, Ordering::Relaxed);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keys() {
        let mut k1 = -1;
        let mut k2 = -1;
        // SAFETY: valid pointers.
        unsafe {
            assert_eq!(pthread_key_create(&mut k1, None), 0);
            assert_eq!(pthread_key_create(&mut k2, None), 0);
        }
        assert_ne!(k1, k2);
        assert!(pthread_getspecific(k1).is_null());
        assert_eq!(pthread_setspecific(k1, 42 as *const c_void), 0);
        assert_eq!(pthread_getspecific(k1) as usize, 42);
        assert!(pthread_getspecific(k2).is_null());
        assert_eq!(pthread_setspecific(999, ptr::null()), Errno::EINVAL.0);
        assert_eq!(pthread_key_delete(k1), 0);
        assert_eq!(pthread_key_delete(k1), Errno::EINVAL.0);
        assert_eq!(pthread_setspecific(k1, ptr::null()), Errno::EINVAL.0);
        assert_eq!(pthread_key_delete(k2), 0);
    }

    #[test]
    fn attrs() {
        let mut a = DEFAULT_ATTR;
        // SAFETY: valid pointers.
        unsafe {
            assert_eq!(pthread_attr_init(&mut a), 0);
            let mut v = 0;
            assert_eq!(pthread_attr_getdetachstate(&a, &mut v), 0);
            assert_eq!(v, 0);
            assert_eq!(pthread_attr_setdetachstate(&mut a, 1), 0);
            assert_eq!(pthread_attr_setdetachstate(&mut a, 7), Errno::EINVAL.0);
            assert_eq!(pthread_attr_setstacksize(&mut a, 100), Errno::EINVAL.0);
            assert_eq!(pthread_attr_setstacksize(&mut a, 1 << 20), 0);
            let mut s = 0;
            assert_eq!(pthread_attr_getstacksize(&a, &mut s), 0);
            assert_eq!(s, 1 << 20);
        }
        assert_eq!(pthread_equal(pthread_self(), pthread_self()), 1);
    }
}
