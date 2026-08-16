//! # filament
//!
//! A high-performance data-parallelism library with rayon-style
//! ergonomics: parallel iterators over standard library types, a
//! work-stealing `join` primitive, and extension traits so that any type
//! can provide its own parallel iterator implementations.
//!
//! ```
//! use filament::prelude::*;
//!
//! let sum: u64 = (0..1_000_000u64).into_par_iter().map(|i| i * i).sum();
//! ```

#![deny(unsafe_op_in_unsafe_fn)]
#![allow(unsafe_op_in_unsafe_fn)] // the core follows rayon's raw-pointer discipline
#![warn(missing_debug_implementations)]

mod job;
mod join;
mod latch;
mod registry;
mod thread_pool;
mod unwind;

pub mod iter;
pub mod prelude;
pub mod range;
pub mod slice;
pub mod vec;

pub use join::{join, join_context, FnContext};
pub use registry::current_num_threads;
pub use thread_pool::{ThreadPool, ThreadPoolBuildError, ThreadPoolBuilder};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_basic() {
        let (a, b) = join(|| 1 + 1, || 2 + 2);
        assert_eq!((a, b), (2, 4));
    }

    fn fib(n: u32) -> u64 {
        if n < 2 {
            return n as u64;
        }
        let (a, b) = join(|| fib(n - 1), || fib(n - 2));
        a + b
    }

    #[test]
    fn join_recursive_fib() {
        assert_eq!(fib(20), 6765);
    }

    #[test]
    fn join_deeply_nested() {
        fn depth(n: usize) -> usize {
            if n == 0 {
                return 0;
            }
            let (a, _) = join(|| depth(n - 1), || ());
            a + 1
        }
        assert_eq!(depth(500), 500);
    }

    #[test]
    fn join_panic_a_propagates() {
        let result = std::panic::catch_unwind(|| {
            join(|| panic!("boom-a"), || 42);
        });
        assert!(result.is_err());
    }

    #[test]
    fn join_panic_b_propagates() {
        let result = std::panic::catch_unwind(|| {
            join(|| 42, || panic!("boom-b"));
        });
        assert!(result.is_err());
    }

    #[test]
    fn join_many_parallel_iterations() {
        // Hammer the scheduler: lots of concurrent joins from the main
        // thread in a loop, so sleep/wake paths get exercised.
        for i in 0..2000 {
            let (a, b) = join(|| i * 2, || i * 3);
            assert_eq!(a, i * 2);
            assert_eq!(b, i * 3);
        }
    }

    #[test]
    fn custom_pool_runs_ops() {
        let pool = ThreadPoolBuilder::new().num_threads(2).build().unwrap();
        assert_eq!(pool.current_num_threads(), 2);
        let r = pool.install(|| {
            let (a, b) = join(|| 10, || 20);
            a + b
        });
        assert_eq!(r, 30);
    }

    #[test]
    fn current_num_threads_positive() {
        assert!(current_num_threads() >= 1);
    }
}
