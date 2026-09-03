//! Internal synchronisation primitives.
//!
//! These are used by the library itself (stdio, `atexit`, the allocator).
//! The C `pthread_*` API is layered on top of the same futex primitives
//! but lives in [`crate::thread`].

use crate::sys;
use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicU32, Ordering};

/// Lock states of [`RawMutex::state`].
const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;

/// Load-only spin iterations before a contended acquire sleeps.
const SPIN: u32 = 40;

/// A small futex based mutex.
///
/// Uncontended lock/unlock is a single atomic operation; waiters sleep in
/// the kernel. The lock word holds only the lock bit and a second word
/// counts the threads sleeping (or about to sleep) on it, the design musl
/// uses. It is not recursive.
///
/// This was chosen over the classic three-state futex mutex (unlocked,
/// locked, contended; what glibc uses) by measurement on a four-thread
/// producer/consumer workload, where it was 5-10x faster: the three-state
/// design has no way to tell whether sleepers remain after a contended
/// acquire, so the lock stays "contended" and every unlock makes a
/// `futex_wake` system call that mostly wakes nobody, and each spurious
/// wake-up of a sleeper costs another sleep. With an exact count an unlock
/// only wakes when somebody is actually asleep, and the futex word stays
/// stable while the lock is held, so sleepers are not woken with `EAGAIN`
/// as other waiters arrive.
#[repr(C)]
pub struct RawMutex {
    state: AtomicU32,
    waiters: AtomicU32,
}

impl RawMutex {
    /// Creates an unlocked mutex.
    pub const fn new() -> Self {
        RawMutex {
            state: AtomicU32::new(UNLOCKED),
            waiters: AtomicU32::new(0),
        }
    }

    /// Acquires the lock, blocking if necessary.
    ///
    /// While the process has a single thread no other thread can touch the
    /// state, so a plain load and store replace the (much more expensive)
    /// atomic read-modify-write; once a thread is created every path uses
    /// the atomics, and the transition is ordered by the `clone` system
    /// call itself. glibc and musl make the same optimisation.
    #[inline]
    pub fn lock(&self) {
        if !crate::thread::is_threaded() {
            if self.state.load(Ordering::Relaxed) == UNLOCKED {
                self.state.store(LOCKED, Ordering::Relaxed);
                return;
            }
        } else if self.try_lock() {
            return;
        }
        self.lock_slow();
    }

    /// Spins briefly, reading only, so waiters do not fight the holder for
    /// the cache line; most critical sections are tiny. Spinning stops as
    /// soon as somebody is asleep on the lock: barging past a sleeper only
    /// burns CPU and delays it further. Returns true if the lock was
    /// acquired.
    #[inline]
    fn spin(&self) -> bool {
        for _ in 0..SPIN {
            if self.state.load(Ordering::Relaxed) == UNLOCKED {
                if self.try_lock() {
                    return true;
                }
            } else if self.waiters.load(Ordering::Relaxed) != 0 {
                return false;
            } else {
                core::hint::spin_loop();
            }
        }
        false
    }

    /// Sleeps until the lock can be taken. `wait` blocks while the state
    /// is `LOCKED`, returning false on timeout.
    ///
    /// The waiter count is incremented (a full barrier) before the state
    /// is re-read, and an unlock stores the state before it reads the
    /// count, so either the unlock sees us and wakes us or we see the lock
    /// free; `futex_wait` fails with `EAGAIN` if the release lands in
    /// between.
    #[inline]
    fn sleep(&self, wait: impl Fn() -> bool) -> bool {
        self.waiters.fetch_add(1, Ordering::SeqCst);
        let ok = loop {
            if self.state.load(Ordering::SeqCst) == UNLOCKED && self.try_lock() {
                break true;
            }
            if !wait() {
                break false;
            }
        };
        self.waiters.fetch_sub(1, Ordering::Relaxed);
        ok
    }

    #[cold]
    fn lock_slow(&self) {
        if self.spin() {
            return;
        }
        self.sleep(|| {
            let _ = sys::futex_wait(&self.state, LOCKED, None);
            true
        });
    }

    /// Acquires the lock, giving up at `deadline` (absolute, on `clock`).
    /// Returns false on timeout.
    pub fn lock_until(&self, deadline: &crate::sys::Timespec, clock: core::ffi::c_int) -> bool {
        if self.try_lock() || self.spin() {
            return true;
        }
        self.sleep(|| {
            !matches!(
                sys::futex_wait_abs(&self.state, LOCKED, deadline, clock),
                Err(crate::errno::Errno::ETIMEDOUT)
            )
        })
    }

    /// Resets the lock to unlocked without waking anyone. For use in a
    /// forked child, where no other thread exists.
    pub fn force_unlock(&self) {
        self.state.store(UNLOCKED, Ordering::Release);
        self.waiters.store(0, Ordering::Relaxed);
    }

    /// Whether the lock is currently held (racy; for diagnostics).
    pub fn is_locked(&self) -> bool {
        self.state.load(Ordering::Relaxed) != UNLOCKED
    }

    /// Tries to acquire the lock without blocking.
    #[inline]
    pub fn try_lock(&self) -> bool {
        self.state
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    /// Releases the lock.
    ///
    /// # Safety
    /// The caller must hold the lock.
    #[inline]
    pub unsafe fn unlock(&self) {
        if !crate::thread::is_threaded() {
            // No other thread exists, so nobody can be waiting.
            self.state.store(UNLOCKED, Ordering::Relaxed);
            return;
        }
        // Sequentially consistent so the store is ordered before the load
        // of the count (see `sleep`); on x86 that is one `xchg`.
        self.state.store(UNLOCKED, Ordering::SeqCst);
        if self.waiters.load(Ordering::SeqCst) != 0 {
            let _ = sys::futex_wake(&self.state, 1);
        }
    }
}

impl Default for RawMutex {
    fn default() -> Self {
        Self::new()
    }
}

/// A mutex protecting a value, in the style of `std::sync::Mutex` but
/// without poisoning.
pub struct Mutex<T> {
    raw: RawMutex,
    value: UnsafeCell<T>,
}

// SAFETY: the lock serialises access to the value.
unsafe impl<T: Send> Sync for Mutex<T> {}
// SAFETY: as above.
unsafe impl<T: Send> Send for Mutex<T> {}

impl<T> Mutex<T> {
    /// Creates a new mutex holding `value`.
    pub const fn new(value: T) -> Self {
        Mutex {
            raw: RawMutex::new(),
            value: UnsafeCell::new(value),
        }
    }

    /// Locks the mutex and returns a guard giving access to the value.
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.raw.lock();
        MutexGuard { mutex: self }
    }

    /// The underlying lock, for code that must lock without a guard
    /// (the `fork` handlers).
    pub fn raw(&self) -> &RawMutex {
        &self.raw
    }

    /// Raw access to the value for callers that hold the raw lock.
    pub fn value_ptr(&self) -> *mut T {
        self.value.get()
    }
}

/// RAII guard returned by [`Mutex::lock`].
pub struct MutexGuard<'a, T> {
    mutex: &'a Mutex<T>,
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: the guard holds the lock.
        unsafe { &*self.mutex.value.get() }
    }
}

impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the guard holds the lock and is unique.
        unsafe { &mut *self.mutex.value.get() }
    }
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: the guard holds the lock.
        unsafe { self.mutex.raw.unlock() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn uncontended() {
        let m = Mutex::new(5);
        *m.lock() += 1;
        assert_eq!(*m.lock(), 6);
        assert!(m.raw.try_lock());
        assert!(!m.raw.try_lock());
        // SAFETY: we hold the lock.
        unsafe { m.raw.unlock() };
    }

    #[test]
    fn contended_counter() {
        let m = Arc::new(Mutex::new(0u64));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let m = m.clone();
                std::thread::spawn(move || {
                    for _ in 0..10_000 {
                        *m.lock() += 1;
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        assert_eq!(*m.lock(), 80_000);
        assert_eq!(m.raw.state.load(Ordering::Relaxed), UNLOCKED);
    }
}
