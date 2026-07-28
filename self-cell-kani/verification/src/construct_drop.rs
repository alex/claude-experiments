//! The core lifecycle: build a cell, then drop it.
//!
//! Obligations discharged here:
//!
//! * `new` allocates, moves the owner in, and builds the dependent in place
//!   without any memory error (Kani's default pointer/overflow checks).
//! * `Drop` runs the dependent's destructor *before* the owner's — the
//!   `unsafe_self_cell` code drops the fields by hand rather than relying on
//!   declaration order, so this is a real proof obligation.
//! * Each of owner and dependent is destroyed exactly once. No leak, no double
//!   free.
//! * The self-reference is still dereferenceable while the dependent's
//!   destructor runs.

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
fn new_then_drop_is_memory_safe() {
    let payload: u32 = kani::any();

    let cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));
    drop(cell);
}

#[kani::proof]
fn drop_runs_dependent_before_owner() {
    let payload: u32 = kani::any();

    {
        let _cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

        assert_eq!(tracking::owner_drop_count(), 0);
        assert_eq!(tracking::dependent_drop_count(), 0);
    }

    assert_eq!(tracking::owner_drop_count(), 1, "owner dropped exactly once");
    assert_eq!(
        tracking::dependent_drop_count(),
        1,
        "dependent dropped exactly once"
    );

    let owner_at = tracking::owner_dropped_at();
    let dependent_at = tracking::dependent_dropped_at();
    assert!(owner_at != 0 && dependent_at != 0);
    assert!(
        dependent_at < owner_at,
        "dependent must be destroyed before the owner it borrows"
    );
}

/// Building two cells and dropping them in the opposite order exercises the
/// allocator interaction: each cell must free exactly its own allocation.
#[kani::proof]
fn two_cells_drop_out_of_order() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();

    let first = Cell::new(Owner::new(a), |owner| Dependent::build(owner));
    let second = Cell::new(Owner::new(b), |owner| Dependent::build(owner));

    assert_eq!(first.borrow_dependent().owner.payload, a);
    assert_eq!(second.borrow_dependent().owner.payload, b);

    drop(first);

    // `second` must be entirely unaffected by `first`'s deallocation.
    assert_eq!(second.borrow_dependent().owner.payload, b);
    assert!(second.borrow_owner().is_alive());

    drop(second);

    assert_eq!(tracking::owner_drop_count(), 2);
    assert_eq!(tracking::dependent_drop_count(), 2);
}

/// Moving the cell must not disturb the self-reference: the whole point of the
/// heap indirection is that the `JoinedCell` never moves.
#[kani::proof]
fn cell_survives_being_moved() {
    let payload: u32 = kani::any();

    let cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));
    let moved = cell;
    let boxed = Box::new(moved);
    let unboxed = *boxed;

    assert_eq!(unboxed.borrow_owner().payload, payload);
    assert_eq!(
        unboxed.borrow_dependent().derived,
        Dependent::expected(payload)
    );
    assert!(core::ptr::eq(
        unboxed.borrow_dependent().owner,
        unboxed.borrow_owner()
    ));
}
