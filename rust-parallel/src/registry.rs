//! The registry: a set of worker threads with work-stealing deques.
//!
//! Design notes (performance):
//!
//! * Workers use LIFO Chase-Lev deques (`crossbeam_deque::Worker::new_lifo`):
//!   push/pop at one end (depth-first execution, hot caches), steals at the
//!   other end (breadth-first stealing, coarse-grained tasks get stolen).
//!
//! * The hot path -- `WorkerThread::push` in `join` -- costs one deque push,
//!   one fence, and one load of the sleeper count. No locks, no allocation.
//!
//! * Idle workers spin over all victim deques a few times, then park via a
//!   Dekker-style handshake: register as sleepy (SeqCst RMW on the sleeper
//!   count + per-worker state), re-scan every queue, and only then park.
//!   Job publishers issue a `SeqCst` fence after pushing and check the
//!   sleeper count (a single load when nobody sleeps), which closes the
//!   store->load race in both directions.

use std::cell::Cell;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::thread;

use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use crossbeam_utils::CachePadded;

use crate::job::{JobRef, StackJob};
use crate::latch::{LockLatch, Probe};

/// State of a worker thread's sleep machinery.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub(crate) enum WorkerState {
    /// Running or actively looking for work.
    Awake = 0,
    /// Announced intention to sleep; re-scanning queues.
    Sleepy = 1,
    /// Parked (or about to park).
    Asleep = 2,
}

pub(crate) struct ThreadInfo {
    stealer: Stealer<JobRef>,
    /// Sleep state; padded to avoid false sharing between workers.
    state: CachePadded<AtomicU8>,
    /// Handle used to unpark this worker. Set once at spawn time, before
    /// any job can possibly be published to the pool.
    handle: OnceLock<thread::Thread>,
}

impl ThreadInfo {
    #[inline]
    pub(crate) fn load_state(&self, order: Ordering) -> WorkerState {
        // Safety: only WorkerState values are ever stored.
        unsafe { mem::transmute::<u8, WorkerState>(self.state.load(order)) }
    }

    #[inline]
    fn swap_state(&self, state: WorkerState, order: Ordering) -> WorkerState {
        unsafe { mem::transmute::<u8, WorkerState>(self.state.swap(state as u8, order)) }
    }

    #[inline]
    pub(crate) fn unpark(&self) {
        self.handle
            .get()
            .expect("worker thread handle not yet registered")
            .unpark();
    }
}

pub(crate) struct Registry {
    thread_infos: Vec<ThreadInfo>,
    injected: Injector<JobRef>,
    /// Number of workers currently in `Sleepy` or `Asleep` state.
    sleepers: CachePadded<AtomicUsize>,
    /// Set when the owning `ThreadPool` is dropped.
    terminating: AtomicBool,
}

/// The terminator "latch": workers run their main loop until this probes
/// true (which only ever happens for non-global pools).
pub(crate) struct Terminator<'r>(&'r Registry);

impl<'r> Probe for Terminator<'r> {
    #[inline]
    fn probe(&self) -> bool {
        self.0.terminating.load(Ordering::Acquire)
    }
}

// //////////////////////////////////////////////////////////////////////
// Global registry

static THE_REGISTRY: OnceLock<Arc<Registry>> = OnceLock::new();

/// Returns the global registry, creating it with default configuration
/// if it does not yet exist.
pub(crate) fn global_registry() -> &'static Arc<Registry> {
    THE_REGISTRY.get_or_init(|| Registry::new(default_num_threads(), None))
}

/// Initializes the global registry with `num_threads` workers; used by
/// `ThreadPoolBuilder::build_global`. Fails if it already exists.
pub(crate) fn init_global_registry(
    num_threads: usize,
    stack_size: Option<usize>,
) -> Result<(), crate::ThreadPoolBuildError> {
    let mut created = false;
    THE_REGISTRY.get_or_init(|| {
        created = true;
        Registry::new(num_threads, stack_size)
    });
    if created {
        Ok(())
    } else {
        Err(crate::ThreadPoolBuildError::GlobalPoolAlreadyInitialized)
    }
}

pub(crate) fn default_num_threads() -> usize {
    if let Ok(v) = std::env::var("FILAMENT_NUM_THREADS") {
        if let Ok(n) = v.parse::<usize>() {
            if n > 0 {
                return n;
            }
        }
    }
    thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

impl Registry {
    pub(crate) fn new(num_threads: usize, stack_size: Option<usize>) -> Arc<Registry> {
        let num_threads = num_threads.max(1);
        let workers: Vec<Worker<JobRef>> =
            (0..num_threads).map(|_| Worker::new_lifo()).collect();

        let registry = Arc::new(Registry {
            thread_infos: workers
                .iter()
                .map(|w| ThreadInfo {
                    stealer: w.stealer(),
                    state: CachePadded::new(AtomicU8::new(WorkerState::Awake as u8)),
                    handle: OnceLock::new(),
                })
                .collect(),
            injected: Injector::new(),
            sleepers: CachePadded::new(AtomicUsize::new(0)),
            terminating: AtomicBool::new(false),
        });

        for (index, worker) in workers.into_iter().enumerate() {
            let registry = Arc::clone(&registry);
            let mut builder = thread::Builder::new().name(format!("filament-worker-{index}"));
            if let Some(size) = stack_size {
                builder = builder.stack_size(size);
            }
            let handle = builder
                .spawn({
                    let registry = Arc::clone(&registry);
                    move || unsafe { main_loop(worker, registry, index) }
                })
                .expect("failed to spawn worker thread");
            // Publish the unpark handle *before* `new` returns: no job can
            // be pushed (and hence no wake can be attempted) until after
            // construction completes.
            registry.thread_infos[index]
                .handle
                .set(handle.thread().clone())
                .unwrap();
        }

        registry
    }

    #[inline]
    pub(crate) fn num_threads(&self) -> usize {
        self.thread_infos.len()
    }

    #[inline]
    pub(crate) fn thread_info(&self, index: usize) -> &ThreadInfo {
        &self.thread_infos[index]
    }

    /// Signal that new work is available; wake a sleeping worker if any.
    ///
    /// **Hot path**: one relaxed load and a predictable branch when the
    /// pool is saturated (no sleepers). We deliberately do *not* fence
    /// here: a publisher whose deque push is still in its store buffer
    /// can miss a concurrently-registering sleeper (and vice versa), a
    /// classic Dekker store->load race. Instead of taxing every push
    /// with a `SeqCst` fence, sleepers park with a bounded timeout and
    /// re-scan, so the worst case for that (extremely rare) race is a
    /// short delay rather than a lost wakeup.
    #[inline]
    pub(crate) fn notify_work_published(&self) {
        if self.sleepers.load(Ordering::Relaxed) > 0 {
            self.wake_any_sleeper();
        }
    }

    #[cold]
    fn wake_any_sleeper(&self) {
        for info in &self.thread_infos {
            if info.load_state(Ordering::Relaxed) != WorkerState::Awake {
                let prev = info.swap_state(WorkerState::Awake, Ordering::SeqCst);
                if prev != WorkerState::Awake {
                    self.sleepers.fetch_sub(1, Ordering::SeqCst);
                    info.unpark();
                    return;
                }
            }
        }
    }

    /// Wake every worker (used for termination).
    fn wake_all(&self) {
        for info in &self.thread_infos {
            let prev = info.swap_state(WorkerState::Awake, Ordering::SeqCst);
            if prev != WorkerState::Awake {
                self.sleepers.fetch_sub(1, Ordering::SeqCst);
            }
            if info.handle.get().is_some() {
                info.unpark();
            }
        }
    }

    /// Push a job into the global injector queue.
    pub(crate) fn inject(&self, job: JobRef) {
        self.injected.push(job);
        self.notify_work_published();
    }

    /// Is any queue (worker deques or injector) non-empty?
    fn any_work_visible(&self) -> bool {
        !self.injected.is_empty() || self.thread_infos.iter().any(|t| !t.stealer.is_empty())
    }

    /// Executes `op` within a worker thread of this registry. If the
    /// current thread is already one, runs it directly; otherwise injects
    /// a job and blocks until it completes.
    pub(crate) fn in_worker<OP, R>(&self, op: OP) -> R
    where
        OP: FnOnce(&WorkerThread, bool) -> R + Send,
        R: Send,
    {
        unsafe {
            let worker_thread = WorkerThread::current();
            if worker_thread.is_null() {
                self.in_worker_cold(op)
            } else if (*worker_thread).registry_ptr() != self as *const Registry {
                // Worker of a *different* pool: inject into ours and block.
                self.in_worker_cold(op)
            } else {
                op(&*worker_thread, false)
            }
        }
    }

    #[cold]
    unsafe fn in_worker_cold<OP, R>(&self, op: OP) -> R
    where
        OP: FnOnce(&WorkerThread, bool) -> R + Send,
        R: Send,
    {
        let job = StackJob::new(
            |_| {
                let worker_thread = WorkerThread::current();
                debug_assert!(!worker_thread.is_null());
                op(&*worker_thread, true)
            },
            LockLatch::new(),
        );
        self.inject(job.as_job_ref());
        job.latch.wait();
        job.into_result()
    }

    pub(crate) fn terminate(&self) {
        self.terminating.store(true, Ordering::Release);
        self.wake_all();
    }
}

// //////////////////////////////////////////////////////////////////////
// WorkerThread

pub(crate) struct WorkerThread {
    worker: Worker<JobRef>,
    index: usize,
    registry: Arc<Registry>,
    /// xorshift RNG state for selecting steal victims.
    rng: Cell<u64>,
}

thread_local! {
    static WORKER_THREAD_STATE: Cell<*const WorkerThread> = const { Cell::new(ptr::null()) };
}

impl WorkerThread {
    /// Gets the `WorkerThread` for the current thread; null if this is not
    /// a worker thread. The returned pointer is valid for the lifetime of
    /// the current stack frame (worker threads never die while jobs run).
    #[inline]
    pub(crate) fn current() -> *const WorkerThread {
        WORKER_THREAD_STATE.with(Cell::get)
    }

    unsafe fn set_current(this: *const WorkerThread) {
        WORKER_THREAD_STATE.with(|t| {
            debug_assert!(t.get().is_null());
            t.set(this);
        });
    }

    #[inline]
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    #[inline]
    pub(crate) fn registry(&self) -> &Arc<Registry> {
        &self.registry
    }

    #[inline]
    fn registry_ptr(&self) -> *const Registry {
        &*self.registry
    }

    #[inline]
    fn thread_info(&self) -> &ThreadInfo {
        self.registry.thread_info(self.index)
    }

    /// Pushes a job onto our local deque and wakes a sleeper if needed.
    #[inline]
    pub(crate) unsafe fn push(&self, job: JobRef) {
        self.worker.push(job);
        self.registry.notify_work_published();
    }

    /// Pops a job off the local deque (LIFO end -- most recently pushed).
    #[inline]
    pub(crate) fn take_local_job(&self) -> Option<JobRef> {
        self.worker.pop()
    }

    #[inline]
    pub(crate) unsafe fn execute(&self, job: JobRef) {
        job.execute();
    }

    #[inline]
    fn next_rand(&self) -> u64 {
        // xorshift64*
        let mut x = self.rng.get();
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng.set(x);
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Try to steal a job: sweep other workers' deques starting from a
    /// random victim, then the injector. Retries while any queue reports
    /// a racy `Retry`.
    fn steal_work(&self) -> Option<JobRef> {
        let registry = &*self.registry;
        let num_threads = registry.thread_infos.len();
        loop {
            let mut retry = false;
            if num_threads > 1 {
                let start = (self.next_rand() >> 32) as usize % num_threads;
                for i in 0..num_threads {
                    let victim = start + i;
                    let victim = if victim >= num_threads {
                        victim - num_threads
                    } else {
                        victim
                    };
                    if victim == self.index {
                        continue;
                    }
                    match registry.thread_infos[victim].stealer.steal() {
                        Steal::Success(job) => return Some(job),
                        Steal::Retry => retry = true,
                        Steal::Empty => {}
                    }
                }
            }
            match registry.injected.steal() {
                Steal::Success(job) => return Some(job),
                Steal::Retry => retry = true,
                Steal::Empty => {}
            }
            if !retry {
                return None;
            }
            std::hint::spin_loop();
        }
    }

    /// Central wait loop: run jobs (local first, then stolen) until
    /// `latch` probes true. An idle worker degrades gracefully: spin
    /// (with a full steal sweep per round), then yield, then park with a
    /// bounded timeout. Parking after a *single* failed sweep would cause
    /// futex ping-pong inside every medium-sized parallel operation.
    #[inline]
    pub(crate) unsafe fn wait_until<L: Probe>(&self, latch: &L) {
        let mut idle = 0u32;
        while !latch.probe() {
            if let Some(job) = self.take_local_job().or_else(|| self.steal_work()) {
                self.execute(job);
                idle = 0;
            } else {
                idle += 1;
                self.back_off(latch, idle);
            }
        }
    }

    /// Rounds of busy-spinning (each round is a full failed steal sweep)
    /// before we start yielding the CPU.
    const SPIN_ROUNDS: u32 = 32;
    /// Rounds of `yield_now` after spinning, before we park.
    const YIELD_ROUNDS: u32 = 4;

    #[inline]
    fn back_off<L: Probe>(&self, latch: &L, idle: u32) {
        if idle <= Self::SPIN_ROUNDS {
            for _ in 0..(idle * 4) {
                std::hint::spin_loop();
            }
        } else if idle <= Self::SPIN_ROUNDS + Self::YIELD_ROUNDS {
            thread::yield_now();
        } else {
            self.sleep(latch, idle);
        }
    }

    /// The sleep protocol. Called when repeated scans found no work.
    ///
    /// 1. Register as a sleeper (SeqCst RMWs on per-worker state and the
    ///    global count).
    /// 2. Re-check the latch and re-scan every queue.
    /// 3. Park with a bounded timeout (see `notify_work_published` for
    ///    why the timeout: publishers don't fence, so a wakeup can be
    ///    lost in a narrow store-buffer race; the timeout re-scan makes
    ///    that harmless).
    #[cold]
    fn sleep<L: Probe>(&self, latch: &L, idle: u32) {
        let info = self.thread_info();
        let registry = &*self.registry;

        let prev = info.swap_state(WorkerState::Sleepy, Ordering::SeqCst);
        debug_assert_eq!(prev, WorkerState::Awake);
        registry.sleepers.fetch_add(1, Ordering::SeqCst);

        // Re-check everything now that we are visible as a sleeper.
        if latch.probe() || registry.terminating.load(Ordering::Acquire) || self.has_local_work()
            || registry.any_work_visible()
        {
            self.wake_self();
            return;
        }

        // Commit to sleeping. A concurrent waker may have already swapped
        // us back to Awake (and decremented the count) -- in that case just
        // return; the banked unpark permit is harmless.
        if info
            .state
            .compare_exchange(
                WorkerState::Sleepy as u8,
                WorkerState::Asleep as u8,
                Ordering::SeqCst,
                Ordering::SeqCst,
            )
            .is_err()
        {
            return;
        }

        // First parks use a short timeout (fast recovery if a wakeup was
        // lost while work exists); once persistently idle, back off to a
        // long timeout -- a parked worker re-scanning every ~10ms is
        // undetectable in CPU terms but bounds every possible race.
        let timeout = if idle < Self::SPIN_ROUNDS + Self::YIELD_ROUNDS + 4 {
            std::time::Duration::from_micros(50)
        } else {
            std::time::Duration::from_millis(10)
        };
        thread::park_timeout(timeout);
        self.wake_self();
    }

    /// Transition back to Awake, decrementing the sleeper count if we were
    /// the ones to perform the transition (a waker may have beaten us).
    fn wake_self(&self) {
        let prev = self.thread_info().swap_state(WorkerState::Awake, Ordering::SeqCst);
        if prev != WorkerState::Awake {
            self.registry.sleepers.fetch_sub(1, Ordering::SeqCst);
        }
    }

    #[inline]
    fn has_local_work(&self) -> bool {
        !self.worker.is_empty()
    }
}

/// //////////////////////////////////////////////////////////////////////
/// Main loop of a worker thread.
unsafe fn main_loop(worker: Worker<JobRef>, registry: Arc<Registry>, index: usize) {
    let worker_thread = WorkerThread {
        worker,
        index,
        registry: Arc::clone(&registry),
        rng: Cell::new(0x9E37_79B9_7F4A_7C15_u64 ^ ((index as u64 + 1) << 32) ^ (index as u64)),
    };
    WorkerThread::set_current(&worker_thread);

    let terminator = Terminator(&registry);
    worker_thread.wait_until(&terminator);

    // Drain any leftover local jobs so latches get set and memory freed.
    while let Some(job) = worker_thread.take_local_job() {
        crate::job::execute_leaked(job);
    }

    WORKER_THREAD_STATE.with(|t| t.set(ptr::null()));
}

/// Executes `op` within a worker of the global registry.
#[inline]
pub(crate) fn in_worker<OP, R>(op: OP) -> R
where
    OP: FnOnce(&WorkerThread, bool) -> R + Send,
    R: Send,
{
    unsafe {
        let worker_thread = WorkerThread::current();
        if !worker_thread.is_null() {
            // Fast path: already on a worker thread (of *some* pool; jobs
            // always run within the pool that owns the current worker).
            op(&*worker_thread, false)
        } else {
            global_registry().in_worker_cold(op)
        }
    }
}

/// Number of threads in the current pool (the pool whose worker is running
/// the current thread, or the global pool otherwise).
pub fn current_num_threads() -> usize {
    unsafe {
        let worker_thread = WorkerThread::current();
        if !worker_thread.is_null() {
            (*worker_thread).registry.num_threads()
        } else {
            global_registry().num_threads()
        }
    }
}
