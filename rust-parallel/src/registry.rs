//! The registry: a set of worker threads with work-stealing deques.
//!
//! Design notes (performance):
//!
//! * Workers use LIFO Chase-Lev deques (`crossbeam_deque::Worker::new_lifo`):
//!   push/pop at one end (depth-first execution, hot caches), steals at the
//!   other end (breadth-first stealing, coarse-grained tasks get stolen).
//!
//! * The hot path -- `WorkerThread::push` in `join` -- costs one deque
//!   emptiness check and one push. No fences, locks, or allocation.
//!
//! * Idle workers degrade gracefully: pause-spin sweeps, then ~100us of
//!   yield rounds (so back-to-back operations reuse hot workers), then an
//!   exponential park ladder (50us x4, 1ms..128ms) ending in an
//!   *indefinite* park -- a long-idle pool costs zero CPU. Wakeups are
//!   best-effort on the timed tiers -- pushers only check for sleepers
//!   when their deque transitions to non-empty, and successful thieves
//!   pay the signal forward -- keeping the join hot path free of fences
//!   and shared-counter traffic; the indefinite tier closes the wakeup
//!   race with a registered double-scan before committing (see `sleep`).
//!   Workers whose previous idle episode ended parked skip the spin/yield
//!   burn entirely (adaptive spinning), so intermittent light load doesn't
//!   pay ~100us of busy-wait per operation per worker.

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
    /// Duration (ns) of the most recent externally-injected operation;
    /// used to decide whether the *next* external caller should
    /// spin-wait (short ops) or block immediately (long ops, where a
    /// spinning caller would compete with workers for cores).
    last_external_ns: AtomicUsize,
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
            last_external_ns: AtomicUsize::new(0),
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
    /// with a `SeqCst` fence, timed-tier sleepers re-scan on timeout (a
    /// missed signal costs a short delay, never a hang) and the
    /// indefinite tier double-scans while registered before parking.
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
            } else if !ptr::eq((*worker_thread).registry_ptr(), self) {
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
        /// Below this, recent operations count as "short": the caller
        /// spin-waits, saving a futex round trip that would otherwise
        /// dominate the operation's latency.
        const SPIN_WORTHY_NS: usize = 200_000;

        let job = StackJob::new(
            |_| {
                let worker_thread = WorkerThread::current();
                debug_assert!(!worker_thread.is_null());
                op(&*worker_thread, true)
            },
            LockLatch::new(),
        );
        let spin = self.last_external_ns.load(Ordering::Relaxed) < SPIN_WORTHY_NS;
        let start = std::time::Instant::now();
        self.inject(job.as_job_ref());
        job.latch.wait(spin);
        let elapsed_ns = start.elapsed().as_nanos().min(usize::MAX as u128) as usize;
        self.last_external_ns.store(elapsed_ns, Ordering::Relaxed);
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
    /// Pushes since we last checked for sleepers (see `push`).
    pushes_since_notify: Cell<u32>,
    /// Whether the previous idle episode found work before reaching the
    /// park ladder (adaptive spinning: fruitless episodes skip the
    /// spin/yield burn next time).
    spin_worthwhile: Cell<bool>,
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
    pub(crate) fn registry_ptr(&self) -> *const Registry {
        &*self.registry
    }

    #[inline]
    fn thread_info(&self) -> &ThreadInfo {
        self.registry.thread_info(self.index)
    }

    /// Pushes a job onto our local deque and wakes a sleeper if needed.
    ///
    /// The sleeper check reads a shared counter that idle workers write,
    /// so doing it on *every* push makes that cache line ping-pong with
    /// the busiest loops in the system (a `join` per recursion level).
    /// We only check when this push made the deque non-empty -- the only
    /// moment new stealable work "appears" from a sleeper's perspective
    /// -- plus every 64th push as a latency bound. Sleepers additionally
    /// park with bounded timeouts, so a delayed wakeup costs at most a
    /// short stall, never a hang.
    #[inline]
    pub(crate) unsafe fn push(&self, job: JobRef) {
        let was_empty = self.worker.is_empty();
        self.worker.push(job);
        let pushes = self.pushes_since_notify.get() + 1;
        if was_empty || pushes >= 64 {
            self.pushes_since_notify.set(0);
            self.registry.notify_work_published();
        } else {
            self.pushes_since_notify.set(pushes);
        }
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
    ///
    /// **Wake cascade**: pushers only signal sleepers when their deque
    /// *becomes* non-empty (see `push`), so thieves carry the cascade
    /// onward: on a successful steal from a victim that still has more
    /// work, wake another sleeper to come share it. This costs one
    /// read-only check per successful steal (rare) instead of a shared
    /// counter read per push (constant).
    /// `thorough` sweeps every victim (fast response right after running
    /// out of work); the throttled form probes a single random victim,
    /// because a *sustained* full-speed sweep from every idle worker
    /// bombards the busy workers' deque cache lines and measurably slows
    /// their push/pop hot paths (each sweep read forces the owner's next
    /// index write to re-acquire the line exclusively).
    fn steal_work(&self, thorough: bool) -> Option<JobRef> {
        let registry = &*self.registry;
        let num_threads = registry.thread_infos.len();
        loop {
            let mut retry = false;
            if num_threads > 1 {
                let start = (self.next_rand() >> 32) as usize % num_threads;
                let attempts = if thorough { num_threads } else { 1 };
                for i in 0..attempts {
                    let victim = start + i;
                    let victim = if victim >= num_threads {
                        victim - num_threads
                    } else {
                        victim
                    };
                    if victim == self.index {
                        continue;
                    }
                    let stealer = &registry.thread_infos[victim].stealer;
                    match stealer.steal() {
                        Steal::Success(job) => {
                            if !stealer.is_empty() {
                                registry.notify_work_published();
                            }
                            return Some(job);
                        }
                        Steal::Retry => retry = true,
                        Steal::Empty => {}
                    }
                }
            }
            match registry.injected.steal() {
                Steal::Success(job) => {
                    if !registry.injected.is_empty() {
                        registry.notify_work_published();
                    }
                    return Some(job);
                }
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
    /// (with a full steal sweep per round), then yield, then park on an
    /// exponential timeout ladder, and finally park *indefinitely* -- a
    /// long-idle pool burns zero CPU. Parking after a single failed
    /// sweep would cause futex ping-pong inside every medium-sized
    /// parallel operation; conversely, spinning is skipped entirely when
    /// the previous idle episode ended in parking anyway (adaptive
    /// spinning: under intermittent load, wakeups come from the wake
    /// protocol, not from polling, so the spin burn buys nothing).
    #[inline]
    pub(crate) unsafe fn wait_until<L: Probe>(&self, latch: &L) {
        let mut idle = 0u32;
        while !latch.probe() {
            let job = self
                .take_local_job()
                .or_else(|| self.steal_work(idle < 4));
            if let Some(job) = job {
                if idle > 0 {
                    // Work arrived while we were still in the cheap
                    // (pre-ladder) phase? Then staying hot paid off.
                    self.spin_worthwhile
                        .set(idle <= Self::SPIN_ROUNDS + Self::YIELD_ROUNDS + Self::SHORT_PARKS);
                }
                self.execute(job);
                idle = 0;
            } else {
                if idle == 0 && !self.spin_worthwhile.get() {
                    // Last episode ended parked: skip the spin/yield burn
                    // *and* the 50us-park tier, straight to millisecond
                    // parks. Cheap because parked workers are woken by
                    // unpark, not by their timeouts -- the timeout is only
                    // the missed-signal backstop.
                    idle = Self::SPIN_ROUNDS + Self::YIELD_ROUNDS + Self::SHORT_PARKS;
                }
                idle = idle.saturating_add(1);
                if !self.back_off(latch, idle) {
                    // Sleep aborted because work looked available: go back
                    // to spinning for it rather than re-running the
                    // (shared-counter RMW) sleep protocol every round.
                    idle = Self::SPIN_ROUNDS / 2;
                }
            }
        }
    }

    /// Rounds of busy-spinning (each round is a full failed steal sweep)
    /// before we start yielding the CPU.
    const SPIN_ROUNDS: u32 = 32;
    /// Rounds of `yield_now` after spinning, before we park. Sized so the
    /// total awake-idle window is ~100us: parallel operations issued
    /// back-to-back (the common pattern in a parallel section of a real
    /// program) then reuse still-hot workers instead of paying a futex
    /// wake chain per operation.
    const YIELD_ROUNDS: u32 = 64;
    /// Number of 50us parks (fast recovery tier) before the exponential
    /// ladder starts.
    const SHORT_PARKS: u32 = 4;
    /// Parks on the exponential ladder (1ms, 2ms, ... 128ms). Beyond the
    /// ladder a worker parks indefinitely and costs nothing until woken.
    const LADDER_PARKS: u32 = 8;

    /// Returns false if a sleep attempt was aborted because work appears
    /// to be available (caller should resume spinning).
    #[inline]
    fn back_off<L: Probe>(&self, latch: &L, idle: u32) -> bool {
        if idle <= Self::SPIN_ROUNDS {
            // Brief pause-spin: lowest-latency response to work appearing
            // in the first microseconds.
            for _ in 0..(idle * 4) {
                std::hint::spin_loop();
            }
            true
        } else if idle <= Self::SPIN_ROUNDS + Self::YIELD_ROUNDS {
            // Cooperative phase: yields keep us schedulable-hot for
            // ~100us without fighting busy threads (or, on shared/virtual
            // CPUs, the hypervisor) the way sustained pause-spinning does.
            thread::yield_now();
            true
        } else {
            self.sleep(latch, idle)
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
    /// Returns false if the sleep was aborted because work (or the latch)
    /// became visible.
    ///
    /// Park ladder: 4 x 50us (fast recovery for briefly-idle pools), then
    /// 1ms..128ms doubling (bounds the cost of any wakeup the best-effort
    /// publishers elided), then **indefinite** -- a fully idle pool costs
    /// zero CPU and zero wakeups until the wake protocol unparks it.
    ///
    /// The timed tiers are self-backstopping: a missed signal costs at
    /// most the current timeout. The indefinite tier cannot rely on that,
    /// so it closes the store->load race directly: after registering as
    /// a sleeper (SeqCst RMW) we scan, wait ~10us -- orders of magnitude
    /// longer than any store buffer takes to drain, which is the only
    /// window in which a publisher can both miss our registration and
    /// have its push invisible to us -- and scan again before committing
    /// to the park. Any publisher that read a stale sleeper count issued
    /// its push before our registration became visible, so the second
    /// scan is guaranteed to see that push on real hardware.
    #[cold]
    fn sleep<L: Probe>(&self, latch: &L, idle: u32) -> bool {
        let info = self.thread_info();
        let registry = &*self.registry;

        // Cheap pre-check before touching any shared-writable state.
        if latch.probe() || self.has_local_work() || registry.any_work_visible() {
            return false;
        }

        let prev = info.swap_state(WorkerState::Sleepy, Ordering::SeqCst);
        debug_assert_eq!(prev, WorkerState::Awake);
        registry.sleepers.fetch_add(1, Ordering::SeqCst);

        // Re-check everything now that we are visible as a sleeper.
        if latch.probe() || registry.terminating.load(Ordering::Acquire) || self.has_local_work()
            || registry.any_work_visible()
        {
            self.wake_self();
            return false;
        }

        // Which park tier are we on?
        let parks = idle.saturating_sub(Self::SPIN_ROUNDS + Self::YIELD_ROUNDS);
        let timeout = if parks <= Self::SHORT_PARKS {
            Some(std::time::Duration::from_micros(50))
        } else if parks <= Self::SHORT_PARKS + Self::LADDER_PARKS {
            let exp = (parks - Self::SHORT_PARKS - 1).min(7);
            Some(std::time::Duration::from_millis(1 << exp))
        } else {
            None
        };

        if timeout.is_none() {
            // Deep-sleep grace: give any in-flight publisher store many
            // orders of magnitude longer than a store buffer can hold it,
            // then take one final registered look.
            for _ in 0..4096 {
                std::hint::spin_loop();
            }
            if latch.probe()
                || registry.terminating.load(Ordering::Acquire)
                || self.has_local_work()
                || registry.any_work_visible()
            {
                self.wake_self();
                return false;
            }
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
            return true;
        }

        match timeout {
            Some(t) => thread::park_timeout(t),
            // May return spuriously (std allows it); the wait loop simply
            // re-scans and re-parks, so correctness never depends on how
            // long a park lasts.
            None => thread::park(),
        }
        self.wake_self();
        true
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
        pushes_since_notify: Cell::new(0),
        spin_worthwhile: Cell::new(true),
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
