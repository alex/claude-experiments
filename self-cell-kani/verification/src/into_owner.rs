//! `into_owner` — the trickiest path in the crate.
//!
//! It has to drop the dependent, move the owner out of the heap allocation with
//! a raw `ptr::read`, free the allocation, and return the owner — all without
//! the owner being dropped, double-dropped, or read after the dependent's
//! destructor could still reach it. It also `transmute`s the generated struct
//! to `UnsafeSelfCell`, which is only sound because of `#[repr(transparent)]`.

use self_cell::self_cell;

use crate::tracking::{self, Dependent, Owner};

self_cell!(
    struct Cell {
        owner: Owner,

        #[covariant]
        dependent: Dependent,
    }
);

#[kani::proof]
fn into_owner_recovers_the_owner_exactly_once() {
    let payload: u32 = kani::any();

    let cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

    let owner = cell.into_owner();

    // The dependent is gone, the owner is not.
    assert_eq!(tracking::dependent_drop_count(), 1);
    assert_eq!(tracking::owner_drop_count(), 0, "owner must not be dropped");

    assert_eq!(owner.payload, payload);
    assert!(owner.is_alive(), "recovered owner must not be poisoned");

    drop(owner);

    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}

/// The dependent's destructor must run *before* the owner is moved out of the
/// allocation, otherwise it would read a moved-from value.
#[kani::proof]
fn dependent_is_destroyed_before_owner_is_moved_out() {
    let payload: u32 = kani::any();

    let cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));
    let dropped_before = tracking::dependent_drop_count();
    assert_eq!(dropped_before, 0);

    let owner = cell.into_owner();

    let dependent_at = tracking::dependent_dropped_at();
    assert!(dependent_at != 0, "dependent must have been destroyed");
    assert_eq!(
        tracking::owner_dropped_at(),
        0,
        "owner must still be undropped at this point"
    );

    drop(owner);
    assert!(tracking::owner_dropped_at() > dependent_at);
}

/// `into_owner` must free the cell's allocation. Interleaving it with a second
/// live cell checks that it frees *its own* allocation and nothing else.
#[kani::proof]
fn into_owner_frees_only_its_own_allocation() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();

    let first = Cell::new(Owner::new(a), |owner| Dependent::build(owner));
    let second = Cell::new(Owner::new(b), |owner| Dependent::build(owner));

    let recovered = first.into_owner();
    assert_eq!(recovered.payload, a);

    assert_eq!(second.borrow_owner().payload, b);
    assert!(second.borrow_owner().is_alive());
    assert_eq!(second.borrow_dependent().derived, Dependent::expected(b));

    drop(second);
    drop(recovered);

    assert_eq!(tracking::owner_drop_count(), 2);
    assert_eq!(tracking::dependent_drop_count(), 2);
}

/// Mutating the dependent first and then consuming the cell mixes the
/// `borrow_mut` and `into_owner` paths over one allocation.
#[kani::proof]
fn into_owner_after_mutation() {
    let payload: u32 = kani::any();

    let mut cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));
    cell.with_dependent_mut(|_owner, dependent| {
        dependent.scratch = dependent.scratch.wrapping_add(1);
    });

    let owner = cell.into_owner();
    assert_eq!(owner.payload, payload);
    assert!(owner.is_alive());
}
