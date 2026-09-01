//! Internal synchronisation primitives.
//!
//! These are used by the library itself (stdio, `atexit`, the allocator).
//! The C `pthread_*` API is layered on top of the same futex primitives
//! but lives in [`crate::thread`].

use crate::sys;
use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicU32, Ordering};

/// Lock states of [`RawMutex`].
const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const CONTENDED: u32 = 2;

/// A small futex based mutex (the classic three-state design).
///
/// Uncontended lock/unlock is a single atomic operation; waiters sleep in
/// the kernel. It is not recursive. `pthread_mutex_t` embeds one, so the
/// layout is a single `u32`.
#[repr(transparent)]
pub struct RawMutex {
    state: AtomicU32,
}

impl RawMutex {
    /// Creates an unlocked mutex.
    pub const fn new() -> Self {
        RawMutex {
            state: AtomicU32::new(UNLOCKED),
        }
    }

    /// Acquires the lock, blocking if necessary.
    #[inline]
    pub fn lock(&self) {
        if self
            .state
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            self.lock_slow();
        }
    }

    #[cold]
    fn lock_slow(&self) {
        // Spin briefly first: most critical sections are tiny.
        for _ in 0..64 {
            if self.state.load(Ordering::Relaxed) == UNLOCKED
                && self
                    .state
                    .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                return;
            }
            core::hint::spin_loop();
        }
        // Mark the lock contended and sleep until it is released.
        while self.state.swap(CONTENDED, Ordering::Acquire) != UNLOCKED {
            let _ = sys::futex_wait(&self.state, CONTENDED, None);
        }
    }

    /// Acquires the lock, giving up at `deadline` (absolute, on `clock`).
    /// Returns false on timeout.
    pub fn lock_until(&self, deadline: &crate::sys::Timespec, clock: core::ffi::c_int) -> bool {
        if self.try_lock() {
            return true;
        }
        while self.state.swap(CONTENDED, Ordering::Acquire) != UNLOCKED {
            if let Err(crate::errno::Errno::ETIMEDOUT) =
                sys::futex_wait_abs(&self.state, CONTENDED, deadline, clock)
            {
                return false;
            }
        }
        true
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
        if self.state.swap(UNLOCKED, Ordering::Release) == CONTENDED {
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
