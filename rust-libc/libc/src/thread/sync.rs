//! `pthread_mutex_t`, `pthread_cond_t`, `pthread_rwlock_t`,
//! `pthread_spinlock_t`, `pthread_barrier_t`, `pthread_once_t` and
//! `sem_t`.
//!
//! All of them are small futex-based designs. Layouts are shared with the
//! C headers (`pthread.h`, `semaphore.h`); static initialisers are all
//! zeros, so every type must treat the zero state as "fresh".

use super::tid;
use crate::errno::Errno;
use crate::sync::RawMutex;
use crate::sys::{self, CLOCK_MONOTONIC, CLOCK_REALTIME, Timespec};
use core::ffi::{c_int, c_uint, c_void};
use core::sync::atomic::{AtomicI32, AtomicU32, AtomicU64, AtomicUsize, Ordering};

const MUTEX_NORMAL: u32 = 0;
const MUTEX_RECURSIVE: u32 = 1;
const MUTEX_ERRORCHECK: u32 = 2;

/// Validates a `timespec` deadline.
fn check_deadline(ts: *const Timespec) -> Result<Timespec, Errno> {
    if ts.is_null() {
        return Err(Errno::EINVAL);
    }
    // SAFETY: the caller passed a valid pointer; it is read once.
    let ts = unsafe { ts.read() };
    if ts.tv_nsec < 0 || ts.tv_nsec >= 1_000_000_000 {
        return Err(Errno::EINVAL);
    }
    Ok(ts)
}

/// Futex wait with an optional absolute deadline. Returns
/// `Err(ETIMEDOUT)` on timeout only.
fn wait(
    addr: &AtomicU32,
    expected: u32,
    deadline: Option<&Timespec>,
    clock: c_int,
) -> Result<(), Errno> {
    match deadline {
        None => {
            let _ = sys::futex_wait(addr, expected, None);
            Ok(())
        }
        Some(d) => match sys::futex_wait_abs(addr, expected, d, clock) {
            Err(Errno::ETIMEDOUT) => Err(Errno::ETIMEDOUT),
            _ => Ok(()),
        },
    }
}

/// Untimed futex wait saying whether the thread was actually woken by a
/// wake (true) rather than returning because the value had already
/// changed or a signal arrived (false).
fn wait_woken(addr: &AtomicU32, expected: u32) -> bool {
    // A signal that already happened would make the kernel return
    // EAGAIN; the check here is the same answer without the syscall.
    addr.load(Ordering::SeqCst) == expected && sys::futex_wait_raw(addr, expected, None).is_ok()
}

fn wake_all(addr: &AtomicU32) {
    let _ = sys::futex_wake(addr, i32::MAX);
}

// ---------------------------------------------------------------------
// Mutex.

/// `pthread_mutex_t`.
#[repr(C)]
pub struct Mutex {
    lock: RawMutex,
    kind: u32,
    owner: AtomicU32,
    count: u32,
}

/// `pthread_mutexattr_t`.
#[repr(C)]
pub struct MutexAttr {
    kind: u32,
}

/// `pthread_mutex_init(3)`.
///
/// # Safety
/// `m` must be valid; `attr` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_init(m: *mut Mutex, attr: *const MutexAttr) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        let kind = if attr.is_null() {
            MUTEX_NORMAL
        } else {
            (*attr).kind
        };
        m.write(Mutex {
            lock: RawMutex::new(),
            kind,
            owner: AtomicU32::new(0),
            count: 0,
        });
    }
    0
}

/// `pthread_mutex_destroy(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_destroy(m: *mut Mutex) -> c_int {
    // SAFETY: caller contract.
    if unsafe { (*m).lock.is_locked() } {
        Errno::EBUSY.0
    } else {
        0
    }
}

/// Shared prologue for the lock variants: handles recursion and error
/// checking. `Ok(true)` means the lock was taken by recursion.
///
/// # Safety
/// `m` must be valid.
#[inline]
unsafe fn lock_prologue(m: *mut Mutex) -> Result<bool, Errno> {
    // SAFETY: caller contract.
    unsafe {
        if (*m).kind != MUTEX_NORMAL && (*m).owner.load(Ordering::Relaxed) == tid() {
            if (*m).kind == MUTEX_RECURSIVE {
                if (*m).count == u32::MAX {
                    return Err(Errno::EAGAIN);
                }
                (*m).count += 1;
                return Ok(true);
            }
            return Err(Errno::EDEADLK);
        }
    }
    Ok(false)
}

/// # Safety
/// `m` must be valid and just locked by the caller.
#[inline]
unsafe fn lock_epilogue(m: *mut Mutex) {
    // SAFETY: caller contract.
    unsafe {
        if (*m).kind != MUTEX_NORMAL {
            (*m).owner.store(tid(), Ordering::Relaxed);
            (*m).count = 1;
        }
    }
}

/// `pthread_mutex_lock(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_lock(m: *mut Mutex) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        match lock_prologue(m) {
            Ok(true) => return 0,
            Ok(false) => {}
            Err(e) => return e.0,
        }
        (*m).lock.lock();
        lock_epilogue(m);
    }
    0
}

/// `pthread_mutex_trylock(3)`.
///
/// # Safety
/// `m` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_trylock(m: *mut Mutex) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        match lock_prologue(m) {
            Ok(true) => return 0,
            Ok(false) => {}
            Err(Errno::EDEADLK) => return Errno::EBUSY.0,
            Err(e) => return e.0,
        }
        if !(*m).lock.try_lock() {
            return Errno::EBUSY.0;
        }
        lock_epilogue(m);
    }
    0
}

/// `pthread_mutex_timedlock(3)`.
///
/// # Safety
/// `m` must be valid; `deadline` a valid `timespec`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_timedlock(
    m: *mut Mutex,
    deadline: *const Timespec,
) -> c_int {
    let deadline = match check_deadline(deadline) {
        Ok(d) => d,
        Err(e) => return e.0,
    };
    let deadline = &deadline;
    // SAFETY: caller contract.
    unsafe {
        match lock_prologue(m) {
            Ok(true) => return 0,
            Ok(false) => {}
            Err(e) => return e.0,
        }
        if !(*m).lock.lock_until(deadline, CLOCK_REALTIME) {
            return Errno::ETIMEDOUT.0;
        }
        lock_epilogue(m);
    }
    0
}

/// `pthread_mutex_clocklock(3)`: like `pthread_mutex_timedlock` with an
/// explicit clock (`CLOCK_REALTIME` or `CLOCK_MONOTONIC`).
///
/// # Safety
/// `m` must be valid; `deadline` a valid `timespec`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_clocklock(
    m: *mut Mutex,
    clock: c_int,
    deadline: *const Timespec,
) -> c_int {
    if clock != CLOCK_REALTIME && clock != CLOCK_MONOTONIC {
        return Errno::EINVAL.0;
    }
    let deadline = match check_deadline(deadline) {
        Ok(d) => d,
        Err(e) => return e.0,
    };
    let deadline = &deadline;
    // SAFETY: caller contract.
    unsafe {
        match lock_prologue(m) {
            Ok(true) => return 0,
            Ok(false) => {}
            Err(e) => return e.0,
        }
        if !(*m).lock.lock_until(deadline, clock) {
            return Errno::ETIMEDOUT.0;
        }
        lock_epilogue(m);
    }
    0
}

/// `pthread_mutex_unlock(3)`.
///
/// # Safety
/// `m` must be valid and locked by the caller.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutex_unlock(m: *mut Mutex) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        if (*m).kind != MUTEX_NORMAL {
            if (*m).owner.load(Ordering::Relaxed) != tid() {
                return Errno::EPERM.0;
            }
            if (*m).kind == MUTEX_RECURSIVE && (*m).count > 1 {
                (*m).count -= 1;
                return 0;
            }
            (*m).owner.store(0, Ordering::Relaxed);
            (*m).count = 0;
        }
        (*m).lock.unlock();
    }
    0
}

/// `pthread_mutexattr_init(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutexattr_init(attr: *mut MutexAttr) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*attr).kind = MUTEX_NORMAL };
    0
}

/// `pthread_mutexattr_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_mutexattr_destroy(_attr: *mut MutexAttr) -> c_int {
    0
}

/// `pthread_mutexattr_settype(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutexattr_settype(attr: *mut MutexAttr, kind: c_int) -> c_int {
    if !(MUTEX_NORMAL..=MUTEX_ERRORCHECK).contains(&(kind as u32)) || kind < 0 {
        return Errno::EINVAL.0;
    }
    // SAFETY: caller contract.
    unsafe { (*attr).kind = kind as u32 };
    0
}

/// `pthread_mutexattr_gettype(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_mutexattr_gettype(
    attr: *const MutexAttr,
    kind: *mut c_int,
) -> c_int {
    // SAFETY: caller contract.
    unsafe { *kind = (*attr).kind as c_int };
    0
}

/// `pthread_mutexattr_setpshared(3)`: process-shared mutexes work the
/// same way (futexes are private, though), so this only validates.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_mutexattr_setpshared(_attr: *mut MutexAttr, pshared: c_int) -> c_int {
    if matches!(pshared, 0 | 1) {
        0
    } else {
        Errno::EINVAL.0
    }
}

// ---------------------------------------------------------------------
// Condition variables.

/// `pthread_cond_t`.
///
/// Waiters sleep on a sequence number that every signal and broadcast
/// bumps. A broadcast does not wake them all: it wakes one and moves the
/// rest onto the mutex's futex (`FUTEX_CMP_REQUEUE`), so they get the
/// mutex one at a time as it is released instead of all waking at once
/// to fight for it (with forty idle workers on one queue that thundering
/// herd was nine tenths of the program's system calls). The mutex's
/// waiter count is raised by the broadcaster for the threads it moves,
/// and each of them lowers it again when it takes the mutex back.
///
/// Timed waits use their own sequence word and are woken rather than
/// moved, because a thread whose wait timed out cannot tell whether it
/// had been moved (and so whether it was counted).
#[repr(C)]
pub struct Cond {
    /// Bumped by every signal and broadcast; untimed waiters sleep on it.
    seq: AtomicU32,
    /// Likewise, for timed waiters.
    seq_timed: AtomicU32,
    /// Untimed threads blocked (or about to block) in a wait, so signals
    /// with nobody waiting skip the futex syscall.
    waiters: AtomicU32,
    /// Timed threads blocked (or about to block).
    waiters_timed: AtomicU32,
    clock: u32,
    _pad: u32,
    /// The mutex the waiters hold (POSIX requires all concurrent waiters
    /// to use the same one), for requeueing.
    mutex: AtomicUsize,
}

/// `pthread_condattr_t`.
#[repr(C)]
pub struct CondAttr {
    clock: u32,
}

/// `pthread_cond_init(3)`.
///
/// # Safety
/// `c` must be valid; `attr` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_init(c: *mut Cond, attr: *const CondAttr) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        let clock = if attr.is_null() {
            CLOCK_REALTIME as u32
        } else {
            (*attr).clock
        };
        c.write(Cond {
            seq: AtomicU32::new(0),
            seq_timed: AtomicU32::new(0),
            waiters: AtomicU32::new(0),
            waiters_timed: AtomicU32::new(0),
            clock,
            _pad: 0,
            mutex: AtomicUsize::new(0),
        });
    }
    0
}

/// `pthread_cond_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_cond_destroy(_c: *mut Cond) -> c_int {
    0
}

/// Shared implementation of the wait functions.
///
/// # Safety
/// `c` and `m` must be valid; `m` locked by the caller.
unsafe fn cond_wait_impl(c: *mut Cond, m: *mut Mutex, deadline: Option<&Timespec>) -> c_int {
    // SAFETY: forwarded.
    unsafe { cond_wait_clock(c, m, (*c).clock as c_int, deadline) }
}

/// [`cond_wait_impl`] with an explicit clock for the deadline.
///
/// # Safety
/// `c` and `m` must be valid; `m` locked by the caller.
unsafe fn cond_wait_clock(
    c: *mut Cond,
    m: *mut Mutex,
    clock: c_int,
    deadline: Option<&Timespec>,
) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        (*c).mutex.store(m as usize, Ordering::Relaxed);
        let lock = &(*m).lock;
        match deadline {
            None => {
                let seq = (*c).seq.load(Ordering::Acquire);
                // Registered while the mutex is still held, so a signaller
                // that takes the mutex afterwards is bound to see us.
                (*c).waiters.fetch_add(1, Ordering::SeqCst);
                let r = pthread_mutex_unlock(m);
                if r != 0 {
                    (*c).waiters.fetch_sub(1, Ordering::SeqCst);
                    return r;
                }
                let woken = wait_woken(&(*c).seq, seq);
                (*c).waiters.fetch_sub(1, Ordering::SeqCst);
                // A thread that was woken (directly, or from the mutex's
                // futex after being moved there) was counted as a mutex
                // waiter by the signaller; one that returned on its own
                // was not.
                if woken {
                    lock.lock_after_wake();
                } else {
                    lock.lock();
                }
                lock_epilogue(m);
                0
            }
            Some(d) => {
                let seq = (*c).seq_timed.load(Ordering::Acquire);
                (*c).waiters_timed.fetch_add(1, Ordering::SeqCst);
                let r = pthread_mutex_unlock(m);
                if r != 0 {
                    (*c).waiters_timed.fetch_sub(1, Ordering::SeqCst);
                    return r;
                }
                let result = wait(&(*c).seq_timed, seq, Some(d), clock);
                (*c).waiters_timed.fetch_sub(1, Ordering::SeqCst);
                pthread_mutex_lock(m);
                match result {
                    Ok(()) => 0,
                    Err(e) => e.0,
                }
            }
        }
    }
}

/// `pthread_cond_wait(3)`.
///
/// # Safety
/// `c` and `m` must be valid; `m` locked by the caller.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_wait(c: *mut Cond, m: *mut Mutex) -> c_int {
    // SAFETY: forwarded.
    unsafe { cond_wait_impl(c, m, None) }
}

/// `pthread_cond_timedwait(3)`.
///
/// # Safety
/// As for [`pthread_cond_wait`]; `deadline` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_timedwait(
    c: *mut Cond,
    m: *mut Mutex,
    deadline: *const Timespec,
) -> c_int {
    let deadline = match check_deadline(deadline) {
        Ok(d) => d,
        Err(e) => return e.0,
    };
    let deadline = &deadline;
    // SAFETY: forwarded.
    unsafe { cond_wait_impl(c, m, Some(deadline)) }
}

/// `pthread_cond_clockwait(3)`.
///
/// # Safety
/// As for [`pthread_cond_timedwait`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_clockwait(
    c: *mut Cond,
    m: *mut Mutex,
    clock: c_int,
    deadline: *const Timespec,
) -> c_int {
    if clock != CLOCK_REALTIME && clock != CLOCK_MONOTONIC {
        return Errno::EINVAL.0;
    }
    let deadline = match check_deadline(deadline) {
        Ok(d) => d,
        Err(e) => return e.0,
    };
    let deadline = &deadline;
    // SAFETY: forwarded.
    unsafe { cond_wait_clock(c, m, clock, Some(deadline)) }
}

/// `pthread_cond_signal(3)`.
///
/// # Safety
/// `c` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_signal(c: *mut Cond) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        // A waiter registers before it drops the mutex, so with none
        // registered nobody can be about to sleep on the current sequence
        // number and the (contended) sequence bump can be skipped.
        if (*c).waiters.load(Ordering::SeqCst) != 0 {
            (*c).seq.fetch_add(1, Ordering::SeqCst);
            let m = (*c).mutex.load(Ordering::Relaxed) as *mut Mutex;
            if m.is_null() {
                let _ = sys::futex_wake(&(*c).seq, 1);
            } else {
                // The woken thread relocks through `lock_after_wake`.
                (*m).lock.add_waiters(1);
                let woken = sys::futex_wake(&(*c).seq, 1).unwrap_or(0) as u32;
                if woken < 1 {
                    (*m).lock.sub_waiters(1 - woken);
                    // Nobody untimed was asleep yet: a timed waiter then.
                    if (*c).waiters_timed.load(Ordering::SeqCst) != 0 {
                        (*c).seq_timed.fetch_add(1, Ordering::SeqCst);
                        let _ = sys::futex_wake(&(*c).seq_timed, 1);
                    }
                }
                return 0;
            }
        }
        if (*c).waiters_timed.load(Ordering::SeqCst) != 0 {
            (*c).seq_timed.fetch_add(1, Ordering::SeqCst);
            let _ = sys::futex_wake(&(*c).seq_timed, 1);
        }
    }
    0
}

/// `pthread_cond_broadcast(3)`.
///
/// # Safety
/// `c` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_cond_broadcast(c: *mut Cond) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        let w = (*c).waiters.load(Ordering::SeqCst);
        if w != 0 {
            (*c).seq.fetch_add(1, Ordering::SeqCst);
            let m = (*c).mutex.load(Ordering::Relaxed) as *mut Mutex;
            if m.is_null() {
                wake_all(&(*c).seq);
            } else {
                // Wake one, move the rest onto the mutex. Every registered
                // waiter is counted as a mutex waiter first; the ones the
                // kernel did not find asleep (they will see the new
                // sequence number and return on their own) are taken back
                // afterwards.
                let lock = &(*m).lock;
                lock.add_waiters(w);
                let moved = loop {
                    let expected = (*c).seq.load(Ordering::SeqCst);
                    match sys::futex_cmp_requeue(
                        &(*c).seq,
                        expected,
                        1,
                        i32::MAX,
                        lock.futex_word(),
                    ) {
                        Ok(n) => break (n as u32).min(w),
                        // Another signaller bumped the sequence meanwhile.
                        Err(Errno::EAGAIN) => continue,
                        Err(_) => {
                            wake_all(&(*c).seq);
                            break w;
                        }
                    }
                };
                if moved < w {
                    lock.sub_waiters(w - moved);
                }
            }
        }
        if (*c).waiters_timed.load(Ordering::SeqCst) != 0 {
            (*c).seq_timed.fetch_add(1, Ordering::SeqCst);
            wake_all(&(*c).seq_timed);
        }
    }
    0
}

/// `pthread_condattr_init(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_condattr_init(attr: *mut CondAttr) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*attr).clock = CLOCK_REALTIME as u32 };
    0
}

/// `pthread_condattr_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_condattr_destroy(_attr: *mut CondAttr) -> c_int {
    0
}

/// `pthread_condattr_setclock(3)`.
///
/// # Safety
/// `attr` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_condattr_setclock(attr: *mut CondAttr, clock: c_int) -> c_int {
    if clock != CLOCK_REALTIME && clock != CLOCK_MONOTONIC {
        return Errno::EINVAL.0;
    }
    // SAFETY: caller contract.
    unsafe { (*attr).clock = clock as u32 };
    0
}

/// `pthread_condattr_getclock(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_condattr_getclock(
    attr: *const CondAttr,
    clock: *mut c_int,
) -> c_int {
    // SAFETY: caller contract.
    unsafe { *clock = (*attr).clock as c_int };
    0
}

/// `pthread_condattr_setpshared(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_condattr_setpshared(_attr: *mut CondAttr, pshared: c_int) -> c_int {
    if matches!(pshared, 0 | 1) {
        0
    } else {
        Errno::EINVAL.0
    }
}

// ---------------------------------------------------------------------
// Read-write locks.

/// `pthread_rwlock_t`. `state` holds the reader count in the low bits,
/// `WRITER` when write-locked and `WRITER_WAITING` while a writer is
/// queued (which stops new readers, so writers are not starved).
#[repr(C)]
pub struct RwLock {
    state: AtomicU32,
    _pad: [u32; 3],
}

const WRITER: u32 = 1 << 31;
const WRITER_WAITING: u32 = 1 << 30;
const READERS: u32 = WRITER_WAITING - 1;

/// `pthread_rwlockattr_t`.
#[repr(C)]
pub struct RwLockAttr {
    _x: u32,
}

/// `pthread_rwlock_init(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_init(l: *mut RwLock, _attr: *const RwLockAttr) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        l.write(RwLock {
            state: AtomicU32::new(0),
            _pad: [0; 3],
        })
    };
    0
}

/// `pthread_rwlock_destroy(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_destroy(l: *mut RwLock) -> c_int {
    // SAFETY: caller contract.
    if unsafe { (*l).state.load(Ordering::Relaxed) } != 0 {
        Errno::EBUSY.0
    } else {
        0
    }
}

/// # Safety
/// `l` must be valid.
unsafe fn rdlock_impl(l: *mut RwLock, deadline: Option<&Timespec>, try_only: bool) -> c_int {
    // SAFETY: caller contract.
    let state = unsafe { &(*l).state };
    loop {
        let s = state.load(Ordering::Relaxed);
        if s & (WRITER | WRITER_WAITING) == 0 {
            if s & READERS == READERS {
                return Errno::EAGAIN.0;
            }
            if state
                .compare_exchange_weak(s, s + 1, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return 0;
            }
            continue;
        }
        if try_only {
            return Errno::EBUSY.0;
        }
        if let Err(e) = wait(state, s, deadline, CLOCK_REALTIME) {
            return e.0;
        }
    }
}

/// # Safety
/// `l` must be valid.
unsafe fn wrlock_impl(l: *mut RwLock, deadline: Option<&Timespec>, try_only: bool) -> c_int {
    // SAFETY: caller contract.
    let state = unsafe { &(*l).state };
    loop {
        let s = state.load(Ordering::Relaxed);
        if s & !WRITER_WAITING == 0 {
            if state
                .compare_exchange_weak(s, WRITER, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return 0;
            }
            continue;
        }
        if try_only {
            return Errno::EBUSY.0;
        }
        // Announce ourselves so readers stop entering, then sleep.
        let announced = s | WRITER_WAITING;
        if s != announced
            && state
                .compare_exchange_weak(s, announced, Ordering::Relaxed, Ordering::Relaxed)
                .is_err()
        {
            continue;
        }
        if let Err(e) = wait(state, announced, deadline, CLOCK_REALTIME) {
            // Leaving without the lock: withdraw the announcement so
            // readers are not held back for a writer that is gone.
            // Another waiting writer re-announces when it wakes.
            state.fetch_and(!WRITER_WAITING, Ordering::Relaxed);
            wake_all(state);
            return e.0;
        }
    }
}

/// `pthread_rwlock_rdlock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_rdlock(l: *mut RwLock) -> c_int {
    // SAFETY: forwarded.
    unsafe { rdlock_impl(l, None, false) }
}

/// `pthread_rwlock_tryrdlock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_tryrdlock(l: *mut RwLock) -> c_int {
    // SAFETY: forwarded.
    unsafe { rdlock_impl(l, None, true) }
}

/// `pthread_rwlock_timedrdlock(3)`.
///
/// # Safety
/// `l` and `deadline` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_timedrdlock(
    l: *mut RwLock,
    deadline: *const Timespec,
) -> c_int {
    match check_deadline(deadline) {
        // SAFETY: forwarded.
        Ok(d) => unsafe { rdlock_impl(l, Some(&d), false) },
        Err(e) => e.0,
    }
}

/// `pthread_rwlock_wrlock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_wrlock(l: *mut RwLock) -> c_int {
    // SAFETY: forwarded.
    unsafe { wrlock_impl(l, None, false) }
}

/// `pthread_rwlock_trywrlock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_trywrlock(l: *mut RwLock) -> c_int {
    // SAFETY: forwarded.
    unsafe { wrlock_impl(l, None, true) }
}

/// `pthread_rwlock_timedwrlock(3)`.
///
/// # Safety
/// `l` and `deadline` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_timedwrlock(
    l: *mut RwLock,
    deadline: *const Timespec,
) -> c_int {
    match check_deadline(deadline) {
        // SAFETY: forwarded.
        Ok(d) => unsafe { wrlock_impl(l, Some(&d), false) },
        Err(e) => e.0,
    }
}

/// `pthread_rwlock_unlock(3)`.
///
/// # Safety
/// `l` must be valid and held by the caller.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_rwlock_unlock(l: *mut RwLock) -> c_int {
    // SAFETY: caller contract.
    let state = unsafe { &(*l).state };
    let s = state.load(Ordering::Relaxed);
    if s & WRITER != 0 {
        state.store(0, Ordering::Release);
        wake_all(state);
    } else {
        let old = state.fetch_sub(1, Ordering::Release);
        if old & READERS == 1 && old & WRITER_WAITING != 0 {
            wake_all(state);
        }
    }
    0
}

/// `pthread_rwlockattr_init(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_rwlockattr_init(_attr: *mut RwLockAttr) -> c_int {
    0
}

/// `pthread_rwlockattr_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_rwlockattr_destroy(_attr: *mut RwLockAttr) -> c_int {
    0
}

// ---------------------------------------------------------------------
// Spin locks.

/// `pthread_spin_init(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_spin_init(l: *mut AtomicI32, _pshared: c_int) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*l).store(0, Ordering::Relaxed) };
    0
}

/// `pthread_spin_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_spin_destroy(_l: *mut AtomicI32) -> c_int {
    0
}

/// `pthread_spin_lock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_spin_lock(l: *mut AtomicI32) -> c_int {
    // SAFETY: caller contract.
    let l = unsafe { &*l };
    while l.load(Ordering::Relaxed) != 0
        || l.compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
    {
        core::hint::spin_loop();
    }
    0
}

/// `pthread_spin_trylock(3)`.
///
/// # Safety
/// `l` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_spin_trylock(l: *mut AtomicI32) -> c_int {
    // SAFETY: caller contract.
    if unsafe { (*l).compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed) }.is_ok() {
        0
    } else {
        Errno::EBUSY.0
    }
}

/// `pthread_spin_unlock(3)`.
///
/// # Safety
/// `l` must be valid and held.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_spin_unlock(l: *mut AtomicI32) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*l).store(0, Ordering::Release) };
    0
}

// ---------------------------------------------------------------------
// Barriers.

/// `pthread_barrier_t`.
#[repr(C)]
pub struct Barrier {
    count: u32,
    _pad: u32,
    /// Arrivals in the current round (low half) and the round number
    /// (high half), packed so an arrival and the round it belongs to are
    /// one atomic step. Waiters sleep on the high half.
    state: AtomicU64,
}

impl Barrier {
    fn generation(&self) -> &AtomicU32 {
        // SAFETY: the high half of the little-endian `u64` is a naturally
        // aligned `u32` inside the same object.
        unsafe { &*((self as *const Barrier as *const u8).add(12) as *const AtomicU32) }
    }
}

/// `pthread_barrierattr_t`.
#[repr(C)]
pub struct BarrierAttr {
    _x: u32,
}

/// `PTHREAD_BARRIER_SERIAL_THREAD`.
pub const BARRIER_SERIAL_THREAD: c_int = -1;

/// `pthread_barrier_init(3)`.
///
/// # Safety
/// `b` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_barrier_init(
    b: *mut Barrier,
    _attr: *const BarrierAttr,
    count: c_uint,
) -> c_int {
    if count == 0 {
        return Errno::EINVAL.0;
    }
    // SAFETY: caller contract.
    unsafe {
        b.write(Barrier {
            count,
            _pad: 0,
            state: AtomicU64::new(0),
        })
    };
    0
}

/// `pthread_barrier_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pthread_barrier_destroy(_b: *mut Barrier) -> c_int {
    0
}

/// `pthread_barrier_wait(3)`.
///
/// # Safety
/// `b` must be an initialised barrier.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_barrier_wait(b: *mut Barrier) -> c_int {
    // SAFETY: caller contract.
    let b = unsafe { &*b };
    let s = b.state.fetch_add(1, Ordering::AcqRel);
    let generation = (s >> 32) as u32;
    if (s as u32) + 1 == b.count {
        // Start the next round: clear the arrivals and bump the round in
        // one step, then release everyone sleeping on the old round.
        b.state
            .fetch_add((1u64 << 32) - b.count as u64, Ordering::AcqRel);
        wake_all(b.generation());
        return BARRIER_SERIAL_THREAD;
    }
    let gen_word = b.generation();
    while gen_word.load(Ordering::Acquire) == generation {
        let _ = sys::futex_wait(gen_word, generation, None);
    }
    0
}

// ---------------------------------------------------------------------
// Once.

/// `pthread_once(3)`.
///
/// # Safety
/// `once` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pthread_once(once: *mut AtomicU32, init: extern "C" fn()) -> c_int {
    // SAFETY: caller contract.
    let once = unsafe { &*once };
    call_once(once, || init());
    0
}

/// Runs `init` exactly once per `once` word (0 = fresh).
pub fn call_once(once: &AtomicU32, init: impl FnOnce()) {
    const RUNNING: u32 = 1;
    const DONE: u32 = 2;
    loop {
        match once.load(Ordering::Acquire) {
            DONE => return,
            RUNNING => {
                let _ = sys::futex_wait(once, RUNNING, None);
            }
            _ => {
                if once
                    .compare_exchange(0, RUNNING, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
                {
                    init();
                    once.store(DONE, Ordering::Release);
                    wake_all(once);
                    return;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// Semaphores.

/// `sem_t`.
#[repr(C)]
pub struct Sem {
    value: AtomicU32,
    waiters: AtomicU32,
    _pad: [u32; 2],
}

/// `SEM_VALUE_MAX`.
pub const SEM_VALUE_MAX: u32 = 0x7fff_ffff;

/// `sem_init(3)`.
///
/// # Safety
/// `s` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_init(s: *mut Sem, _pshared: c_int, value: c_uint) -> c_int {
    if value > SEM_VALUE_MAX {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe {
        s.write(Sem {
            value: AtomicU32::new(value),
            waiters: AtomicU32::new(0),
            _pad: [0; 2],
        })
    };
    0
}

/// `sem_destroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sem_destroy(_s: *mut Sem) -> c_int {
    0
}

/// # Safety
/// `s` must be valid.
unsafe fn sem_wait_impl(s: *mut Sem, deadline: Option<&Timespec>, try_only: bool) -> c_int {
    // SAFETY: caller contract.
    let s = unsafe { &*s };
    loop {
        if !try_only {
            crate::thread::cancel_point();
        }
        let v = s.value.load(Ordering::Relaxed);
        if v > 0 {
            if s.value
                .compare_exchange_weak(v, v - 1, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return 0;
            }
            continue;
        }
        if try_only {
            Errno::EAGAIN.set();
            return -1;
        }
        // The waiter count must be visible before the value is rechecked
        // (in the futex), and a poster's increment before it reads the
        // count: a Dekker handshake, hence SeqCst.
        s.waiters.fetch_add(1, Ordering::SeqCst);
        let r = wait(&s.value, 0, deadline, CLOCK_REALTIME);
        s.waiters.fetch_sub(1, Ordering::SeqCst);
        if let Err(e) = r {
            e.set();
            return -1;
        }
    }
}

/// `sem_wait(3)`.
///
/// # Safety
/// `s` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_wait(s: *mut Sem) -> c_int {
    // SAFETY: forwarded.
    unsafe { sem_wait_impl(s, None, false) }
}

/// `sem_trywait(3)`.
///
/// # Safety
/// `s` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_trywait(s: *mut Sem) -> c_int {
    // SAFETY: forwarded.
    unsafe { sem_wait_impl(s, None, true) }
}

/// `sem_timedwait(3)`.
///
/// # Safety
/// `s` and `deadline` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_timedwait(s: *mut Sem, deadline: *const Timespec) -> c_int {
    match check_deadline(deadline) {
        // SAFETY: forwarded.
        Ok(d) => unsafe { sem_wait_impl(s, Some(&d), false) },
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `sem_post(3)`.
///
/// # Safety
/// `s` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_post(s: *mut Sem) -> c_int {
    // SAFETY: caller contract.
    let s = unsafe { &*s };
    loop {
        let v = s.value.load(Ordering::Relaxed);
        if v == SEM_VALUE_MAX {
            Errno::EOVERFLOW.set();
            return -1;
        }
        if s.value
            .compare_exchange_weak(v, v + 1, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            break;
        }
    }
    if s.waiters.load(Ordering::SeqCst) > 0 {
        let _ = sys::futex_wake(&s.value, 1);
    }
    0
}

/// `sem_getvalue(3)`.
///
/// # Safety
/// Both pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sem_getvalue(s: *mut Sem, out: *mut c_int) -> c_int {
    // SAFETY: caller contract.
    unsafe { *out = (*s).value.load(Ordering::Relaxed) as c_int };
    0
}

/// Keeps `c_void` referenced for the header-facing signatures.
#[allow(dead_code)]
fn _void(_: *mut c_void) {}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;

    #[test]
    fn layouts() {
        assert_eq!(core::mem::size_of::<Mutex>(), 20);
        assert_eq!(core::mem::size_of::<Cond>(), 32);
        assert_eq!(core::mem::size_of::<RwLock>(), 16);
        assert_eq!(core::mem::size_of::<Barrier>(), 16);
        assert_eq!(core::mem::size_of::<Sem>(), 16);
    }

    #[test]
    fn mutex_kinds() {
        let mut m = MaybeUninit::<Mutex>::zeroed();
        let m = m.as_mut_ptr();
        // SAFETY: valid storage.
        unsafe {
            assert_eq!(pthread_mutex_lock(m), 0);
            assert_eq!(pthread_mutex_trylock(m), Errno::EBUSY.0);
            assert_eq!(pthread_mutex_unlock(m), 0);
            assert_eq!(pthread_mutex_destroy(m), 0);
            let mut attr = MutexAttr { kind: 0 };
            assert_eq!(pthread_mutexattr_settype(&mut attr, 1), 0);
            assert_eq!(pthread_mutex_init(m, &attr), 0);
            assert_eq!(pthread_mutex_lock(m), 0);
            assert_eq!(pthread_mutex_lock(m), 0);
            assert_eq!(pthread_mutex_trylock(m), 0);
            assert_eq!(pthread_mutex_unlock(m), 0);
            assert_eq!(pthread_mutex_unlock(m), 0);
            assert_eq!(pthread_mutex_destroy(m), Errno::EBUSY.0);
            assert_eq!(pthread_mutex_unlock(m), 0);
            assert_eq!(pthread_mutex_unlock(m), Errno::EPERM.0);
            assert_eq!(pthread_mutexattr_settype(&mut attr, 2), 0);
            assert_eq!(pthread_mutex_init(m, &attr), 0);
            assert_eq!(pthread_mutex_lock(m), 0);
            assert_eq!(pthread_mutex_lock(m), Errno::EDEADLK.0);
            assert_eq!(pthread_mutex_unlock(m), 0);
            assert_eq!(pthread_mutex_unlock(m), Errno::EPERM.0);
        }
    }

    #[test]
    fn rwlock_and_sem_single_thread() {
        let mut l = MaybeUninit::<RwLock>::zeroed();
        let l = l.as_mut_ptr();
        // SAFETY: valid storage.
        unsafe {
            assert_eq!(pthread_rwlock_rdlock(l), 0);
            assert_eq!(pthread_rwlock_rdlock(l), 0);
            assert_eq!(pthread_rwlock_trywrlock(l), Errno::EBUSY.0);
            assert_eq!(pthread_rwlock_unlock(l), 0);
            assert_eq!(pthread_rwlock_unlock(l), 0);
            assert_eq!(pthread_rwlock_wrlock(l), 0);
            assert_eq!(pthread_rwlock_tryrdlock(l), Errno::EBUSY.0);
            assert_eq!(pthread_rwlock_unlock(l), 0);
            assert_eq!(pthread_rwlock_destroy(l), 0);
        }
        let mut s = MaybeUninit::<Sem>::zeroed();
        let s = s.as_mut_ptr();
        // SAFETY: valid storage.
        unsafe {
            assert_eq!(sem_init(s, 0, 2), 0);
            assert_eq!(sem_wait(s), 0);
            assert_eq!(sem_wait(s), 0);
            assert_eq!(sem_trywait(s), -1);
            assert_eq!(Errno::get(), Errno::EAGAIN);
            assert_eq!(sem_post(s), 0);
            let mut v = 0;
            assert_eq!(sem_getvalue(s, &mut v), 0);
            assert_eq!(v, 1);
            let past = Timespec {
                tv_sec: 1,
                tv_nsec: 0,
            };
            assert_eq!(sem_wait(s), 0);
            assert_eq!(sem_timedwait(s, &past), -1);
            assert_eq!(Errno::get(), Errno::ETIMEDOUT);
        }
    }

    #[test]
    fn threads_contend_on_mutex_cond_and_rwlock() {
        use std::sync::Arc;
        struct Shared(
            MaybeUninit<Mutex>,
            MaybeUninit<Cond>,
            MaybeUninit<RwLock>,
            std::cell::UnsafeCell<u64>,
        );
        // SAFETY: access is synchronised by the primitives under test.
        unsafe impl Sync for Shared {}
        unsafe impl Send for Shared {}
        let shared = Arc::new(Shared(
            MaybeUninit::zeroed(),
            MaybeUninit::zeroed(),
            MaybeUninit::zeroed(),
            std::cell::UnsafeCell::new(0),
        ));
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let s = shared.clone();
                std::thread::spawn(move || {
                    let m = s.0.as_ptr() as *mut Mutex;
                    let l = s.2.as_ptr() as *mut RwLock;
                    for _ in 0..5000 {
                        // SAFETY: the primitives are valid.
                        unsafe {
                            pthread_mutex_lock(m);
                            *s.3.get() += 1;
                            pthread_mutex_unlock(m);
                            // The rwlock guards nothing the mutex guards.
                            pthread_rwlock_wrlock(l);
                            let _ = *s.3.get();
                            pthread_rwlock_unlock(l);
                            pthread_rwlock_rdlock(l);
                            let _ = *s.3.get();
                            pthread_rwlock_unlock(l);
                        }
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        // SAFETY: all threads are done.
        assert_eq!(unsafe { *shared.3.get() }, 20_000);

        // Condition variable hand-off.
        let s = shared.clone();
        // SAFETY: the primitives are valid.
        unsafe { *s.3.get() = 0 };
        let waiter = std::thread::spawn(move || {
            let m = s.0.as_ptr() as *mut Mutex;
            let c = s.1.as_ptr() as *mut Cond;
            // SAFETY: the primitives are valid.
            unsafe {
                pthread_mutex_lock(m);
                while *s.3.get() == 0 {
                    pthread_cond_wait(c, m);
                }
                let v = *s.3.get();
                pthread_mutex_unlock(m);
                v
            }
        });
        std::thread::sleep(std::time::Duration::from_millis(20));
        let m = shared.0.as_ptr() as *mut Mutex;
        let c = shared.1.as_ptr() as *mut Cond;
        // SAFETY: the primitives are valid.
        unsafe {
            pthread_mutex_lock(m);
            *shared.3.get() = 7;
            pthread_cond_broadcast(c);
            pthread_mutex_unlock(m);
        }
        assert_eq!(waiter.join().unwrap(), 7);
        // Timed wait that must time out.
        let now = sys::clock_gettime(CLOCK_REALTIME).unwrap();
        let deadline = Timespec {
            tv_sec: now.tv_sec,
            tv_nsec: now.tv_nsec + 10_000_000,
        };
        let deadline = if deadline.tv_nsec >= 1_000_000_000 {
            Timespec {
                tv_sec: deadline.tv_sec + 1,
                tv_nsec: deadline.tv_nsec - 1_000_000_000,
            }
        } else {
            deadline
        };
        // SAFETY: the primitives are valid.
        unsafe {
            pthread_mutex_lock(m);
            assert_eq!(pthread_cond_timedwait(c, m, &deadline), Errno::ETIMEDOUT.0);
            pthread_mutex_unlock(m);
        }
        // once
        let once = AtomicU32::new(0);
        let mut n = 0;
        call_once(&once, || n += 1);
        call_once(&once, || n += 1);
        assert_eq!(n, 1);
    }
}
