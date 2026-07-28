//! `try_new` and `try_new_or_recover`.
//!
//! Both write the owner into a fresh allocation, arm an `OwnerAndCellDropGuard`
//! and then run a builder that may fail. The two failure paths are deliberately
//! different, and the difference is exactly where a double free would live:
//!
//! * `try_new` lets the guard run — it drops the owner and frees the cell.
//! * `try_new_or_recover` `ptr::read`s the owner back out, `mem::forget`s the
//!   guard so the owner is not also dropped in place, and frees the allocation
//!   by hand.
//!
//! The builder's error type is chosen so that the harness explores both the
//! success and the failure branch.

use self_cell::self_cell;

use crate::tracking::{self, Dependent, Owner};

self_cell!(
    struct Cell {
        owner: Owner,

        #[covariant]
        dependent: Dependent,
    }
);

#[derive(Debug, PartialEq, Eq)]
struct BuildError(u32);

#[kani::proof]
fn try_new_success_matches_new() {
    let payload: u32 = kani::any();

    let cell = Cell::try_new(Owner::new(payload), |owner| {
        Ok::<_, BuildError>(Dependent::build(owner))
    })
    .unwrap();

    assert_eq!(cell.borrow_owner().payload, payload);
    assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));

    drop(cell);
    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}

/// On failure `try_new` consumes the owner: it must be dropped exactly once,
/// and the allocation freed, with no dependent ever having existed.
#[kani::proof]
fn try_new_failure_consumes_owner_exactly_once() {
    let payload: u32 = kani::any();
    let code: u32 = kani::any();

    let result = Cell::try_new(Owner::new(payload), |owner| {
        // Touch the owner in its final resting place before bailing out.
        assert!(owner.is_alive());
        assert_eq!(owner.payload, payload);
        Err::<Dependent<'_>, _>(BuildError(code))
    });

    match result {
        Ok(_) => unreachable!(),
        Err(err) => assert_eq!(err, BuildError(code)),
    }

    assert_eq!(tracking::owner_drop_count(), 1, "owner dropped exactly once");
    assert_eq!(
        tracking::dependent_drop_count(),
        0,
        "no dependent was ever constructed"
    );
}

/// Both branches under one nondeterministic condition, so Kani proves the two
/// paths agree on the accounting rather than checking them in isolation.
#[kani::proof]
fn try_new_either_branch_is_balanced() {
    let payload: u32 = kani::any();
    let should_fail: bool = kani::any();

    let result = Cell::try_new(Owner::new(payload), |owner| {
        if should_fail {
            Err(BuildError(owner.payload))
        } else {
            Ok(Dependent::build(owner))
        }
    });

    match result {
        Ok(cell) => {
            assert!(!should_fail);
            assert_eq!(cell.borrow_owner().payload, payload);
            drop(cell);
        }
        Err(err) => {
            assert!(should_fail);
            assert_eq!(err, BuildError(payload));
        }
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}

/// On failure `try_new_or_recover` hands the owner *back*. It must be the same
/// value, not dropped, and not left dangling in a freed allocation.
#[kani::proof]
fn try_new_or_recover_failure_returns_live_owner() {
    let payload: u32 = kani::any();
    let code: u32 = kani::any();

    let result = Cell::try_new_or_recover(Owner::new(payload), |owner| {
        assert!(owner.is_alive());
        Err::<Dependent<'_>, _>(BuildError(code))
    });

    let (owner, err) = match result {
        Ok(_) => unreachable!(),
        Err(pair) => pair,
    };

    assert_eq!(err, BuildError(code));
    assert_eq!(
        tracking::owner_drop_count(),
        0,
        "recovered owner must not have been dropped in place"
    );
    assert!(owner.is_alive(), "recovered owner must not be poisoned");
    assert_eq!(owner.payload, payload);

    drop(owner);
    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 0);
}

#[kani::proof]
fn try_new_or_recover_either_branch_is_balanced() {
    let payload: u32 = kani::any();
    let should_fail: bool = kani::any();

    let result = Cell::try_new_or_recover(Owner::new(payload), |owner| {
        if should_fail {
            Err(BuildError(owner.payload))
        } else {
            Ok(Dependent::build(owner))
        }
    });

    match result {
        Ok(cell) => {
            assert!(!should_fail);
            assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));
            drop(cell);
            assert_eq!(tracking::dependent_drop_count(), 1);
        }
        Err((owner, err)) => {
            assert!(should_fail);
            assert_eq!(err, BuildError(payload));
            assert_eq!(owner.payload, payload);
            drop(owner);
            assert_eq!(tracking::dependent_drop_count(), 0);
        }
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}

/// A failed `try_new_or_recover` followed by a successful one, reusing the
/// recovered owner. If the first call freed the allocation incorrectly, or
/// returned an owner that still aliased it, this would show up here.
#[kani::proof]
fn recovered_owner_can_be_reused() {
    let payload: u32 = kani::any();

    let owner = match Cell::try_new_or_recover(Owner::new(payload), |_| {
        Err::<Dependent<'_>, _>(BuildError(0))
    }) {
        Ok(_) => unreachable!(),
        Err((owner, _err)) => owner,
    };

    let cell = Cell::new(owner, |owner| Dependent::build(owner));

    assert_eq!(cell.borrow_owner().payload, payload);
    assert!(cell.borrow_owner().is_alive());
    assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));

    drop(cell);
    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}
