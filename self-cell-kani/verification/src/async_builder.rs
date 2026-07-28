//! The `async_builder` construction path.
//!
//! With `#[covariant, async_builder]` the three constructors become `async fn`s
//! taking `AsyncFnOnce` builders. The generated body is the same as the sync
//! one with an `.await` in the middle — which means the armed drop guard, the
//! raw field pointers and the half-initialised `JoinedCell` are all live across
//! a suspension point, and the future can be dropped there. That is what
//! `SendMutPtr` and the `Send` impl on `OwnerAndCellDropGuard` exist for.
//!
//! Two Kani constraints shape how these are written:
//!
//! * Kani 0.67 cannot lower `async` *closures* (`FIXME(async_closures): Lower
//!   these to SMIR`), so every builder here is a free `async fn` item. Since a
//!   free function captures nothing, the nondeterministic choices the harnesses
//!   need are passed through statics instead.
//! * `kani::block_on` does not converge in reasonable time, so the futures are
//!   polled by hand. All the builders below are immediately ready except the
//!   cancellation one, which never is.

use core::future::Future;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use core::task::{Context, Poll, Waker};

use self_cell::self_cell;

use crate::tracking::{self, Dependent, Owner};

self_cell!(
    struct AsyncCell {
        owner: Owner,

        #[covariant, async_builder]
        dependent: Dependent,
    }
);

/// Drives a future that is expected to complete without ever yielding.
fn poll_ready<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    let mut cx = Context::from_waker(Waker::noop());

    match future.as_mut().poll(&mut cx) {
        Poll::Ready(value) => value,
        Poll::Pending => unreachable!("builder future must complete immediately"),
    }
}

#[derive(Debug, PartialEq, Eq)]
struct BuildError(u32);

/// Stands in for what an `async` closure would have captured.
static SHOULD_FAIL: AtomicBool = AtomicBool::new(false);
static ERROR_CODE: AtomicU32 = AtomicU32::new(0);

async fn build_ok(owner: &Owner) -> Dependent<'_> {
    assert!(owner.is_alive());
    Dependent::build(owner)
}

async fn build_fallible(owner: &Owner) -> Result<Dependent<'_>, BuildError> {
    assert!(owner.is_alive());
    if SHOULD_FAIL.load(Ordering::Relaxed) {
        Err(BuildError(ERROR_CODE.load(Ordering::Relaxed)))
    } else {
        Ok(Dependent::build(owner))
    }
}

async fn build_never(owner: &Owner) -> Dependent<'_> {
    core::future::pending::<()>().await;
    Dependent::build(owner)
}

#[kani::proof]
fn async_new_then_drop() {
    let payload: u32 = kani::any();

    let cell = poll_ready(AsyncCell::new(Owner::new(payload), build_ok));

    assert_eq!(cell.borrow_owner().payload, payload);
    assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));

    drop(cell);

    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}

#[kani::proof]
fn async_try_new_either_branch_is_balanced() {
    let payload: u32 = kani::any();
    let should_fail: bool = kani::any();
    let code: u32 = kani::any();

    SHOULD_FAIL.store(should_fail, Ordering::Relaxed);
    ERROR_CODE.store(code, Ordering::Relaxed);

    let result = poll_ready(AsyncCell::try_new(Owner::new(payload), build_fallible));

    match result {
        Ok(cell) => {
            assert!(!should_fail);
            assert_eq!(cell.borrow_owner().payload, payload);
            assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));
            drop(cell);
            assert_eq!(tracking::dependent_drop_count(), 1);
        }
        Err(err) => {
            assert!(should_fail);
            assert_eq!(err, BuildError(code));
            assert_eq!(tracking::dependent_drop_count(), 0);
        }
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}

#[kani::proof]
fn async_try_new_or_recover_either_branch_is_balanced() {
    let payload: u32 = kani::any();
    let should_fail: bool = kani::any();
    let code: u32 = kani::any();

    SHOULD_FAIL.store(should_fail, Ordering::Relaxed);
    ERROR_CODE.store(code, Ordering::Relaxed);

    let result = poll_ready(AsyncCell::try_new_or_recover(
        Owner::new(payload),
        build_fallible,
    ));

    match result {
        Ok(cell) => {
            assert!(!should_fail);
            assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));
            drop(cell);
            assert_eq!(tracking::dependent_drop_count(), 1);
        }
        Err((owner, err)) => {
            assert!(should_fail);
            assert_eq!(err, BuildError(code));
            assert_eq!(
                tracking::owner_drop_count(),
                0,
                "the recovered owner must not have been dropped in place"
            );
            assert!(owner.is_alive());
            assert_eq!(owner.payload, payload);
            drop(owner);
            assert_eq!(tracking::dependent_drop_count(), 0);
        }
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}

/// Dropping the constructor's future before it completes is the cancellation
/// path: the owner has already been moved into the allocation, so the armed
/// `OwnerAndCellDropGuard` is what has to clean it up. This is the one place
/// the guard is reachable through the public API under Kani, since cancelling
/// needs no unwinding.
#[kani::proof]
fn cancelling_construction_cleans_up() {
    let payload: u32 = kani::any();

    {
        let mut future = Box::pin(AsyncCell::new(Owner::new(payload), build_never));

        let mut cx = Context::from_waker(Waker::noop());
        assert!(future.as_mut().poll(&mut cx).is_pending());
        assert_eq!(
            tracking::owner_drop_count(),
            0,
            "the owner is live inside the allocation while suspended"
        );

        // Cancel.
    }

    assert_eq!(
        tracking::owner_drop_count(),
        1,
        "cancelling must destroy the owner exactly once"
    );
    assert_eq!(tracking::dependent_drop_count(), 0);
}
