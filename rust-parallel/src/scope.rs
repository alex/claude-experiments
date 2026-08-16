//! `scope` and `spawn`: structured (and unstructured) task parallelism
//! for jobs that don't fit the iterator model.

use std::any::Any;
use std::marker::PhantomData;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::job::HeapJob;
use crate::latch::Probe;
use crate::registry::{self, Registry, WorkerState, WorkerThread};
use crate::unwind;

/// Represents a fork-join scope which can be used to spawn any number of
/// tasks that may reference stack data with lifetime `'scope`. See
/// [`scope`] for details.
pub struct Scope<'scope> {
    registry: Arc<Registry>,
    /// Index of the worker thread that owns (waits on) this scope.
    owner_index: usize,
    /// Pending job count: 1 for the scope body + 1 per outstanding spawn.
    /// When it reaches 0 the owner is released (and unparked if asleep).
    counter: AtomicUsize,
    /// First panic from any spawned job.
    panic: AtomicPtr<Box<dyn Any + Send + 'static>>,
    /// Invariant over 'scope: the closures we accept may borrow data
    /// that lives exactly as long as 'scope.
    marker: PhantomData<Box<dyn FnOnce(&Scope<'scope>) + Send + Sync + 'scope>>,
}

/// Creates a "fork-join" scope and invokes the closure with a reference
/// to it. Tasks spawned inside may borrow anything that outlives the
/// scope; `scope` does not return until all spawned tasks complete.
///
/// ```
/// let mut left = 0;
/// let mut right = 0;
/// filament::scope(|s| {
///     s.spawn(|_| left = 1);
///     s.spawn(|_| right = 1);
/// });
/// assert_eq!(left + right, 2);
/// ```
pub fn scope<'scope, OP, R>(op: OP) -> R
where
    OP: FnOnce(&Scope<'scope>) -> R + Send,
    R: Send,
{
    registry::in_worker(|owner, _| {
        let scope = Scope::<'scope> {
            registry: Arc::clone(owner.registry()),
            owner_index: owner.index(),
            counter: AtomicUsize::new(1),
            panic: AtomicPtr::new(ptr::null_mut()),
            marker: PhantomData,
        };
        let result = unwind::halt_unwinding(|| op(&scope));
        // Release the scope body's own hold on the counter, then work
        // (or steal) until every spawned job has finished.
        scope.release_one();
        unsafe {
            owner.wait_until(&ScopeDone(&scope));
        }
        match result {
            Ok(r) => {
                scope.maybe_propagate_panic();
                r
            }
            Err(payload) => {
                // The body itself panicked: still waited for spawned jobs
                // (they may borrow stack data), now propagate.
                unwind::resume_unwinding(payload)
            }
        }
    })
}

struct ScopeDone<'a, 'scope>(&'a Scope<'scope>);

impl<'a, 'scope> Probe for ScopeDone<'a, 'scope> {
    #[inline]
    fn probe(&self) -> bool {
        self.0.counter.load(Ordering::Acquire) == 0
    }
}

impl<'scope> Scope<'scope> {
    /// Spawns a job into the fork-join scope. The job runs on any pool
    /// thread and may itself spawn more jobs into `self`.
    pub fn spawn<BODY>(&self, body: BODY)
    where
        BODY: FnOnce(&Scope<'scope>) + Send + 'scope,
    {
        self.counter.fetch_add(1, Ordering::Relaxed);
        let scope_ptr = ScopePtr(self as *const Self);
        let job = HeapJob::new(move || {
            // Safety: the scope waits for our counter decrement before it
            // is destroyed, so the pointer is valid for the entire run.
            let scope = unsafe { &*scope_ptr.get() };
            match unwind::halt_unwinding(|| body(scope)) {
                Ok(()) => {}
                Err(payload) => scope.job_panicked(payload),
            }
            scope.release_one();
        });
        // Safety: lifetimes are erased here, which is sound because the
        // scope cannot return until the job runs (counter protocol).
        let job_ref = unsafe { job.into_job_ref() };
        unsafe {
            let worker = WorkerThread::current();
            if !worker.is_null() && ptr::eq((*worker).registry_ptr(), &*self.registry) {
                (*worker).push(job_ref);
            } else {
                self.registry.inject(job_ref);
            }
        }
    }

    fn job_panicked(&self, payload: Box<dyn Any + Send + 'static>) {
        // Keep the first panic; drop the rest.
        let boxed: Box<Box<dyn Any + Send + 'static>> = Box::new(payload);
        let raw = Box::into_raw(boxed);
        if self
            .panic
            .compare_exchange(ptr::null_mut(), raw, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            // Another panic got there first.
            unsafe { drop(Box::from_raw(raw)) };
        }
    }

    fn maybe_propagate_panic(&self) {
        let raw = self.panic.swap(ptr::null_mut(), Ordering::Acquire);
        if !raw.is_null() {
            let payload = unsafe { *Box::from_raw(raw) };
            unwind::resume_unwinding(payload);
        }
    }

    /// Decrement the pending-job counter; on reaching zero, wake the
    /// owner if it is parked.
    fn release_one(&self) {
        // Read everything needed *before* the decrement: the moment the
        // counter hits 0 the owner may return and free the Scope.
        let registry: *const Registry = &*self.registry;
        let owner_index = self.owner_index;
        if self.counter.fetch_sub(1, Ordering::SeqCst) == 1 {
            // `self` may now dangle; `registry` stays alive via the
            // calling worker (same pool) or the owner itself.
            unsafe {
                let info = (*registry).thread_info(owner_index);
                if info.load_state(Ordering::SeqCst) != WorkerState::Awake {
                    info.unpark();
                }
            }
        }
    }
}

impl<'scope> std::fmt::Debug for Scope<'scope> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Scope")
            .field("pending", &self.counter.load(Ordering::Relaxed))
            .finish()
    }
}

/// A raw pointer that is Send (the scope protocol guarantees validity
/// across threads). Accessed via a method so closures capture the whole
/// `Send` wrapper, not the raw-pointer field (2021 disjoint capture).
struct ScopePtr<T>(*const T);
unsafe impl<T: Sync> Send for ScopePtr<T> {}

impl<T> ScopePtr<T> {
    #[inline]
    fn get(&self) -> *const T {
        self.0
    }
}

/// Puts the task into the global thread pool's queue, to run whenever a
/// thread is free. The task must be `'static`; for borrowing tasks use
/// [`scope`].
///
/// A panic inside a spawned task cannot be propagated anywhere, so it
/// aborts the process (matching rayon's default behavior).
pub fn spawn<F>(func: F)
where
    F: FnOnce() + Send + 'static,
{
    let job = HeapJob::new(|| {
        if let Err(payload) = unwind::halt_unwinding(func) {
            let msg = payload
                .downcast_ref::<&str>()
                .copied()
                .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
                .unwrap_or("<non-string panic payload>");
            eprintln!("filament: detached spawn task panicked: {msg}; aborting");
            std::process::abort();
        }
    });
    let job_ref = unsafe { job.into_job_ref() };
    unsafe {
        let worker = WorkerThread::current();
        if !worker.is_null() {
            (*worker).push(job_ref);
        } else {
            registry::global_registry().inject(job_ref);
        }
    }
}
