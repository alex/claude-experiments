//! Helpers for propagating panics across threads.

use std::any::Any;
use std::panic::{self, AssertUnwindSafe};

/// Executes `f` and captures any panic, translating that panic into a
/// `Err` result. The assumption is that any panic will be propagated
/// later with `resume_unwinding`, so `f` can be treated as unwind safe.
#[inline]
pub(crate) fn halt_unwinding<F, R>(func: F) -> Result<R, Box<dyn Any + Send>>
where
    F: FnOnce() -> R,
{
    panic::catch_unwind(AssertUnwindSafe(func))
}

#[inline]
pub(crate) fn resume_unwinding(payload: Box<dyn Any + Send>) -> ! {
    panic::resume_unwind(payload)
}
