//! Public thread pool API: `ThreadPoolBuilder`, `ThreadPool`.

use std::fmt;
use std::sync::Arc;

use crate::registry::{self, Registry};

/// Error returned when building a thread pool fails.
#[derive(Debug)]
pub enum ThreadPoolBuildError {
    /// The global pool was already initialized.
    GlobalPoolAlreadyInitialized,
}

impl fmt::Display for ThreadPoolBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThreadPoolBuildError::GlobalPoolAlreadyInitialized => {
                write!(f, "the global thread pool has already been initialized")
            }
        }
    }
}

impl std::error::Error for ThreadPoolBuildError {}

/// Builds a [`ThreadPool`] or configures the global pool.
///
/// ```
/// let pool = filament::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
/// let n = pool.install(|| filament::current_num_threads());
/// assert_eq!(n, 2);
/// ```
#[derive(Debug, Default)]
pub struct ThreadPoolBuilder {
    num_threads: usize,
    stack_size: Option<usize>,
}

impl ThreadPoolBuilder {
    pub fn new() -> ThreadPoolBuilder {
        ThreadPoolBuilder {
            num_threads: 0,
            stack_size: None,
        }
    }

    /// Sets the number of worker threads. Zero (the default) means "use
    /// `FILAMENT_NUM_THREADS` or the number of available CPUs".
    pub fn num_threads(mut self, num_threads: usize) -> ThreadPoolBuilder {
        self.num_threads = num_threads;
        self
    }

    /// Sets the stack size (in bytes) for worker threads.
    pub fn stack_size(mut self, stack_size: usize) -> ThreadPoolBuilder {
        self.stack_size = Some(stack_size);
        self
    }

    fn resolved_num_threads(&self) -> usize {
        if self.num_threads > 0 {
            self.num_threads
        } else {
            registry::default_num_threads()
        }
    }

    /// Creates a standalone thread pool.
    pub fn build(self) -> Result<ThreadPool, ThreadPoolBuildError> {
        Ok(ThreadPool {
            registry: Registry::new(self.resolved_num_threads(), self.stack_size),
        })
    }

    /// Initializes the global thread pool. May only be called once, before
    /// any use of the global pool.
    pub fn build_global(self) -> Result<(), ThreadPoolBuildError> {
        registry::init_global_registry(self.resolved_num_threads(), self.stack_size)
    }
}

/// A user-created thread pool, distinct from the global one.
pub struct ThreadPool {
    registry: Arc<Registry>,
}

impl ThreadPool {
    /// Executes `op` within the pool: parallel operations (`join`,
    /// parallel iterators) executed inside `op` use this pool's threads.
    pub fn install<OP, R>(&self, op: OP) -> R
    where
        OP: FnOnce() -> R + Send,
        R: Send,
    {
        self.registry.in_worker(|_, _| op())
    }

    /// The number of worker threads in this pool.
    pub fn current_num_threads(&self) -> usize {
        self.registry.num_threads()
    }

    /// Executes `join` within this pool.
    pub fn join<A, B, RA, RB>(&self, oper_a: A, oper_b: B) -> (RA, RB)
    where
        A: FnOnce() -> RA + Send,
        B: FnOnce() -> RB + Send,
        RA: Send,
        RB: Send,
    {
        self.install(|| crate::join(oper_a, oper_b))
    }

    /// Creates a fork-join scope within this pool.
    pub fn scope<'scope, OP, R>(&self, op: OP) -> R
    where
        OP: FnOnce(&crate::Scope<'scope>) -> R + Send,
        R: Send,
    {
        self.install(|| crate::scope(op))
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        self.registry.terminate();
    }
}

impl fmt::Debug for ThreadPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ThreadPool")
            .field("num_threads", &self.current_num_threads())
            .finish()
    }
}
