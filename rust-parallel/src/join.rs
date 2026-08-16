//! The `join` primitive: potentially-parallel divide and conquer.

use crate::job::StackJob;
use crate::latch::{Probe, SpinLatch};
use crate::registry;
use crate::unwind;

/// Context passed to closures in [`join_context`], indicating whether the
/// closure was *migrated* -- executed on a different thread than the one
/// that called `join_context` (i.e. actually ran in parallel).
#[derive(Debug)]
pub struct FnContext {
    migrated: bool,
    /// Ensure `FnContext` is not `Send` / not constructible by users.
    _marker: std::marker::PhantomData<*mut ()>,
}

impl FnContext {
    #[inline]
    pub(crate) fn new(migrated: bool) -> Self {
        FnContext {
            migrated,
            _marker: std::marker::PhantomData,
        }
    }

    /// Returns `true` if the closure was called from a different thread
    /// than it was declared on.
    #[inline]
    pub fn migrated(&self) -> bool {
        self.migrated
    }
}

/// Takes two closures and *potentially* runs them in parallel. It returns
/// a pair of the results from those closures.
///
/// Conceptually, calling `join()` is similar to spawning two threads, one
/// executing each of the two closures. However, the implementation is
/// very different and incurs very low overhead. The underlying technique
/// is called "work stealing": the second closure is made available to
/// other idle threads, but if none of them take it, it simply runs on the
/// current thread (in which case its cost is one deque push + pop).
///
/// # Panics
///
/// Panics in either closure are propagated to the caller. If both panic,
/// the panic from `oper_a` wins.
///
/// # Examples
///
/// ```
/// let (a, b) = filament::join(|| 1 + 1, || 2 + 2);
/// assert_eq!(a, 2);
/// assert_eq!(b, 4);
/// ```
#[inline]
pub fn join<A, B, RA, RB>(oper_a: A, oper_b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    join_context(|_| oper_a(), |_| oper_b())
}

/// Like [`join`], except the closures receive an [`FnContext`] reporting
/// whether they were migrated to another thread.
#[inline]
pub fn join_context<A, B, RA, RB>(oper_a: A, oper_b: B) -> (RA, RB)
where
    A: FnOnce(FnContext) -> RA + Send,
    B: FnOnce(FnContext) -> RB + Send,
    RA: Send,
    RB: Send,
{
    registry::in_worker(|worker_thread, injected| unsafe {
        // Create the virtual wrapper for `oper_b` on our stack and push a
        // type-erased reference onto our deque for thieves.
        let job_b = StackJob::new(
            |migrated| oper_b(FnContext::new(migrated)),
            SpinLatch::new(worker_thread.registry(), worker_thread.index()),
        );
        let job_b_ref = job_b.as_job_ref();
        let job_b_id = job_b_ref.id();
        worker_thread.push(job_b_ref);

        // Execute `a` (while `b` is up for grabs).
        let status_a = unwind::halt_unwinding(|| oper_a(FnContext::new(injected)));

        // Now try to pop `b` back off our deque: in the common (unstolen)
        // case this succeeds and we run it inline with zero further
        // synchronization.
        while !job_b.latch.probe() {
            if let Some(job) = worker_thread.take_local_job() {
                if job.id() == job_b_id {
                    // `b` was never stolen; run it here and now.
                    match status_a {
                        Ok(result_a) => {
                            let result_b = job_b.run_inline(injected);
                            return (result_a, result_b);
                        }
                        Err(panic_a) => {
                            // `a` panicked and `b` never ran: drop `b` and
                            // propagate.
                            drop(job_b);
                            unwind::resume_unwinding(panic_a);
                        }
                    }
                } else {
                    // A *different* job (pushed by some enclosing join and
                    // uncovered when `b` was stolen). Execute it: it is
                    // independent work, and doing so may keep us busy until
                    // `b`'s thief finishes.
                    worker_thread.execute(job);
                }
            } else {
                // Local deque empty and `b` not yet done: steal from
                // others / park until the latch is set.
                worker_thread.wait_until(&job_b.latch);
                debug_assert!(job_b.latch.probe());
                break;
            }
        }

        // `b` completed on some thread (possibly ours, via the wait loop).
        let result_b = job_b.into_result(); // propagates `b`'s panic
        match status_a {
            Ok(result_a) => (result_a, result_b),
            Err(panic_a) => unwind::resume_unwinding(panic_a),
        }
    })
}
