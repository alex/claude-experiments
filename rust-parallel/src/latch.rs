//! Latches: one-shot signalling primitives used to detect when a stolen
//! job has completed, or when an injected job has finished.
//!
//! The key safety rule (inherited from rayon's design) is that
//! `Latch::set` takes a raw pointer: setting a latch may cause the memory
//! containing it to be invalidated *immediately* (the owner observes the
//! set and pops its stack frame), so implementations must read everything
//! they need out of `this` *before* the final atomic store, and never
//! touch `this` afterwards.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Condvar, Mutex};

use crate::registry::{Registry, WorkerState};

pub(crate) trait Latch {
    /// Set the latch, signalling others.
    ///
    /// # WARNING
    ///
    /// Setting a latch triggers other threads to wake up and (in the case
    /// of blocking latches) to be awoken. The memory of `this` may be
    /// deallocated once the owner thread observes the set, which can
    /// happen *while `set` is still executing*. So no access to `this`
    /// is permitted after the "signalling store".
    unsafe fn set(this: *const Self);
}

/// Anything we can spin/work-steal-wait on.
pub(crate) trait Probe {
    fn probe(&self) -> bool;
}

/// Latch used by a worker thread inside `join`: the owner blocks (after
/// exhausting all opportunities to steal) by parking, and the setter
/// unparks it directly. This gives O(1) targeted wakeup instead of a
/// broadcast.
pub(crate) struct SpinLatch<'r> {
    core: AtomicBool,
    registry: &'r Registry,
    owner_index: usize,
}

impl<'r> SpinLatch<'r> {
    /// Creates a latch owned by worker `owner_index` of `registry`. The
    /// setter must be a worker thread of the *same* registry (which is
    /// always true for `join`: only same-pool workers can steal the job),
    /// since that thief's existence keeps `registry` alive during `set`.
    #[inline]
    pub(crate) fn new(registry: &'r Registry, owner_index: usize) -> SpinLatch<'r> {
        SpinLatch {
            core: AtomicBool::new(false),
            registry,
            owner_index,
        }
    }
}

impl<'r> Probe for SpinLatch<'r> {
    #[inline]
    fn probe(&self) -> bool {
        self.core.load(Ordering::Acquire)
    }
}

impl<'r> Latch for SpinLatch<'r> {
    #[inline]
    unsafe fn set(this: *const Self) {
        // Copy out everything we need *before* the signalling store.
        let registry: *const Registry = (*this).registry;
        let owner_index = (*this).owner_index;

        // SeqCst store: must be totally ordered with the owner's
        // state-store + probe-load sequence (Dekker-style handshake, see
        // `WorkerThread::sleep`).
        (*this).core.store(true, Ordering::SeqCst);
        // `this` may now be dangling! `registry` remains valid because the
        // calling thread is a worker of that registry.

        let info = &(*registry).thread_info(owner_index);
        if info.load_state(Ordering::SeqCst) != WorkerState::Awake {
            info.unpark();
        }
    }
}

/// A latch for signalling an external (non-worker) thread.
///
/// A fast-path atomic flag is checked with a short bounded spin before
/// falling back to a mutex+condvar block: small parallel operations
/// complete in a few microseconds, and eating a futex sleep+wake on
/// every one of them would dominate their latency.
pub(crate) struct LockLatch {
    core: AtomicBool,
    m: Mutex<bool>,
    v: Condvar,
}

impl LockLatch {
    #[inline]
    pub(crate) fn new() -> LockLatch {
        LockLatch {
            core: AtomicBool::new(false),
            m: Mutex::new(false),
            v: Condvar::new(),
        }
    }

    /// Block until the latch is set.
    ///
    /// `spin` enables a bounded spin phase before blocking: worth a
    /// futex round trip (~10us) of latency for short operations, but
    /// actively harmful for long ones -- a spinning external thread is
    /// an extra runnable thread competing with the pool's workers for
    /// cores exactly while they ramp up. Callers pass a hint based on
    /// how long recent operations took.
    ///
    /// Every exit path ends by observing `core`, which is the setter's
    /// *final* memory access: once we return (and possibly destroy the
    /// latch) the setter is provably done touching it.
    pub(crate) fn wait(&self, spin: bool) {
        if spin {
            for i in 0..2048u32 {
                if self.core.load(Ordering::Acquire) {
                    return;
                }
                for _ in 0..(i / 64 + 1) {
                    std::hint::spin_loop();
                }
            }
        }
        {
            let mut guard = self.m.lock().unwrap();
            while !*guard {
                guard = self.v.wait(guard).unwrap();
            }
        }
        // The mutex flag is set, so the setter is past the critical
        // section; it stores `core` immediately after releasing the lock.
        // Spin out those last few nanoseconds.
        while !self.core.load(Ordering::Acquire) {
            std::hint::spin_loop();
        }
    }
}

impl Latch for LockLatch {
    unsafe fn set(this: *const Self) {
        let this = &*this;
        {
            let mut guard = this.m.lock().unwrap();
            *guard = true;
            this.v.notify_all();
        }
        // Final access: after this store any waiter (spinning or woken)
        // may return and invalidate `this`.
        this.core.store(true, Ordering::Release);
    }
}

/// Counting latch, used by `scope`: starts at 1 ("the scope itself") and
/// is incremented for every spawned job. Terminates when it reaches 0.
/// The owner is a worker thread that steal-waits on it.
#[allow(dead_code)]
pub(crate) struct CountLatch<'r> {
    counter: std::sync::atomic::AtomicUsize,
    latch: SpinLatch<'r>,
}

#[allow(dead_code)]
impl<'r> CountLatch<'r> {
    #[inline]
    pub(crate) fn new(registry: &'r Registry, owner_index: usize) -> CountLatch<'r> {
        CountLatch {
            counter: std::sync::atomic::AtomicUsize::new(1),
            latch: SpinLatch::new(registry, owner_index),
        }
    }

    #[inline]
    pub(crate) fn increment(&self) {
        self.counter.fetch_add(1, Ordering::Relaxed);
    }

    /// Decrements the count; if it reaches zero, sets the internal latch.
    /// Same safety contract as `Latch::set`.
    #[inline]
    pub(crate) unsafe fn set(this: *const Self) {
        if (*this).counter.fetch_sub(1, Ordering::SeqCst) == 1 {
            Latch::set(&(*this).latch);
        }
    }
}

impl<'r> Probe for CountLatch<'r> {
    #[inline]
    fn probe(&self) -> bool {
        self.latch.probe()
    }
}

/// A latch for signalling an external thread waiting on a `CountLatch`
/// style counter (scope created from outside the pool).
#[allow(dead_code)]
pub(crate) struct CountLockLatch {
    counter: std::sync::atomic::AtomicUsize,
    latch: LockLatch,
}

#[allow(dead_code)]
impl CountLockLatch {
    #[inline]
    pub(crate) fn new() -> CountLockLatch {
        CountLockLatch {
            counter: std::sync::atomic::AtomicUsize::new(1),
            latch: LockLatch::new(),
        }
    }

    #[inline]
    pub(crate) fn increment(&self) {
        self.counter.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn wait(&self) {
        self.latch.wait(true);
    }

    #[inline]
    pub(crate) unsafe fn set(this: *const Self) {
        if (*this).counter.fetch_sub(1, Ordering::SeqCst) == 1 {
            Latch::set(&(*this).latch);
        }
    }
}
