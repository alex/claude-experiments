//! Type-erased jobs that can be pushed onto the work-stealing deques.
//!
//! The central design constraint is that `join` must not allocate: the
//! closure for the "other half" of a join lives on the stack of the caller
//! (`StackJob`), and only a fat-pointer-sized `JobRef` is pushed onto the
//! deque. The caller guarantees the job outlives any use of the `JobRef`
//! by waiting on a latch before returning.

use std::any::Any;
use std::cell::UnsafeCell;

use crate::latch::Latch;
use crate::unwind;

pub(crate) enum JobResult<T> {
    None,
    Ok(T),
    Panic(Box<dyn Any + Send>),
}

impl<T> JobResult<T> {
    /// Convert the `JobResult` for a job that has finished (and hence
    /// its result is available) into `T`, propagating panics if needed.
    pub(crate) fn into_return_value(self) -> T {
        match self {
            JobResult::None => unreachable!("job function panicked or was cancelled"),
            JobResult::Ok(x) => x,
            JobResult::Panic(x) => unwind::resume_unwinding(x),
        }
    }
}

/// A `Job` is used to advertise work for other threads that they may
/// want to steal. In accordance with time honored tradition, jobs are
/// arranged in a deque, so that thieves can take from the top of the
/// deque while the main worker manages the bottom of the deque.
pub(crate) trait Job {
    /// Unsafe: this may be called from a different thread than the one
    /// which scheduled the job, so the implementer must ensure the
    /// appropriate traits are met, whether `Send`, `Sync`, or both.
    unsafe fn execute(this: *const ());
}

/// Effectively a Job trait object. Each JobRef **must** be executed
/// exactly once, or else data may leak.
///
/// Internally, we store the job's data in a `*const ()` pointer. The
/// true type is something like `*const StackJob<...>`, but we hide
/// it. We also carry the "execute fn" from the `Job` trait.
#[derive(Copy, Clone)]
pub(crate) struct JobRef {
    pointer: *const (),
    execute_fn: unsafe fn(*const ()),
}

unsafe impl Send for JobRef {}
unsafe impl Sync for JobRef {}

impl JobRef {
    /// Unsafe: caller asserts that `data` will remain valid until the
    /// job is executed.
    pub(crate) unsafe fn new<T>(data: *const T) -> JobRef
    where
        T: Job,
    {
        JobRef {
            pointer: data as *const (),
            execute_fn: <T as Job>::execute,
        }
    }

    /// Returns an opaque handle that can be saved and compared, without
    /// making `JobRef` itself `PartialEq`. Only data-pointer identity is
    /// compared: two distinct live jobs always have distinct addresses.
    #[inline]
    pub(crate) fn id(&self) -> *const () {
        self.pointer
    }

    #[inline]
    pub(crate) unsafe fn execute(self) {
        (self.execute_fn)(self.pointer)
    }
}

/// A job that will be owned by a stack slot. This means that when it
/// executes it need not free any heap data, the cleanup occurs when
/// the stack frame is later popped. The function parameter indicates
/// `true` if the job was stolen -- executed on a different thread.
pub(crate) struct StackJob<L, F, R>
where
    L: Latch + Sync,
    F: FnOnce(bool) -> R + Send,
    R: Send,
{
    pub(crate) latch: L,
    func: UnsafeCell<Option<F>>,
    result: UnsafeCell<JobResult<R>>,
}

impl<L, F, R> StackJob<L, F, R>
where
    L: Latch + Sync,
    F: FnOnce(bool) -> R + Send,
    R: Send,
{
    #[inline]
    pub(crate) fn new(func: F, latch: L) -> StackJob<L, F, R> {
        StackJob {
            latch,
            func: UnsafeCell::new(Some(func)),
            result: UnsafeCell::new(JobResult::None),
        }
    }

    #[inline]
    pub(crate) unsafe fn as_job_ref(&self) -> JobRef {
        JobRef::new(self)
    }

    /// Runs the job on the thread that owns it, when it is known that the
    /// job was never stolen (it was just popped back off our own deque).
    /// Skips the latch and the result slot entirely.
    #[inline]
    pub(crate) unsafe fn run_inline(&self, stolen: bool) -> R {
        let func = (*self.func.get()).take().unwrap();
        func(stolen)
    }

    /// Once the latch has been set, extracts the result (or propagates a
    /// panic that occurred while running the job).
    #[inline]
    pub(crate) unsafe fn into_result(self) -> R {
        self.result.into_inner().into_return_value()
    }
}

impl<L, F, R> Job for StackJob<L, F, R>
where
    L: Latch + Sync,
    F: FnOnce(bool) -> R + Send,
    R: Send,
{
    unsafe fn execute(this: *const ()) {
        let this = &*(this as *const Self);
        let func = (*this.func.get()).take().unwrap();
        (*this.result.get()) = match unwind::halt_unwinding(|| func(true)) {
            Ok(x) => JobResult::Ok(x),
            Err(x) => JobResult::Panic(x),
        };
        // The latch set must be the very last access to `this`: as soon as
        // the owner observes the latch it may pop its stack frame,
        // invalidating `this`.
        Latch::set(&this.latch);
    }
}

/// Represents a job stored in the heap. Used to implement `spawn`.
#[allow(dead_code)]
pub(crate) struct HeapJob<BODY>
where
    BODY: FnOnce() + Send,
{
    job: BODY,
}

#[allow(dead_code)]
impl<BODY> HeapJob<BODY>
where
    BODY: FnOnce() + Send,
{
    pub(crate) fn new(job: BODY) -> Box<Self> {
        Box::new(HeapJob { job })
    }

    /// Creates a `JobRef` from this job -- note that this hides all
    /// lifetimes, so it is up to you to ensure that this JobRef
    /// doesn't outlive any data that it closes over.
    pub(crate) unsafe fn into_job_ref(self: Box<Self>) -> JobRef {
        JobRef::new(Box::into_raw(self))
    }
}

impl<BODY> Job for HeapJob<BODY>
where
    BODY: FnOnce() + Send,
{
    unsafe fn execute(this: *const ()) {
        let this = Box::from_raw(this as *mut Self);
        (this.job)();
    }
}

/// Dropping a `JobRef` without executing it would leak the job's data;
/// this guard executes leftover jobs when a deque is torn down.
pub(crate) fn execute_leaked(job: JobRef) {
    // Best effort: run it so that latches get set and memory is freed.
    let _ = unwind::halt_unwinding(|| unsafe { job.execute() });
}
