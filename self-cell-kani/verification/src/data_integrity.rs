//! Accessors return the values that were actually stored.
//!
//! Memory safety alone is not enough: the crate also has to hand back the right
//! bytes. `borrow_owner`, `borrow_dependent`, `with_dependent` and
//! `with_dependent_mut` all reconstruct a typed reference by casting a
//! `NonNull<u8>` back to `JoinedCell<Owner, Dependent>`, so the field offsets
//! have to line up with the ones `_field_pointers` used at construction time.

use self_cell::self_cell;

use crate::tracking::{Dependent, Owner, PlainDependent};

self_cell!(
    struct Cell {
        owner: Owner,

        #[covariant]
        dependent: Dependent,
    }
);

self_cell!(
    struct NotCovariantCell {
        owner: Owner,

        #[not_covariant]
        dependent: PlainDependent,
    }
);

#[kani::proof]
fn accessors_round_trip() {
    let payload: u32 = kani::any();

    let cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

    assert_eq!(cell.borrow_owner().payload, payload);
    assert!(cell.borrow_owner().is_alive());
    assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));

    // The dependent's reference must point at the owner living inside this very
    // cell, not at a copy.
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));

    cell.with_dependent(|owner, dependent| {
        assert_eq!(owner.payload, payload);
        assert_eq!(dependent.derived, Dependent::expected(payload));
        assert!(core::ptr::eq(dependent.owner, owner));
    });
}

#[kani::proof]
fn with_dependent_mut_writes_are_observable() {
    let payload: u32 = kani::any();
    let replacement: u32 = kani::any();

    let mut cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

    let returned = cell.with_dependent_mut(|owner, dependent| {
        assert_eq!(owner.payload, payload);
        let previous = dependent.derived;
        dependent.derived = replacement;
        previous
    });

    assert_eq!(returned, Dependent::expected(payload));

    // The write went to the heap allocation, not to a temporary.
    assert_eq!(cell.borrow_dependent().derived, replacement);
    cell.with_dependent(|_, dependent| assert_eq!(dependent.derived, replacement));

    // ... and it did not disturb the owner.
    assert_eq!(cell.borrow_owner().payload, payload);
    assert!(cell.borrow_owner().is_alive());

    // `Dependent::drop` asserts the invariant `derived == expected(payload)`,
    // so restore it before the cell goes out of scope.
    cell.with_dependent_mut(|owner, dependent| {
        dependent.derived = Dependent::expected(owner.payload);
    });
}

/// `with_dependent_mut` hands out `&Owner` and `&mut Dependent` derived from
/// the same allocation at the same time. They must address disjoint bytes.
#[kani::proof]
fn owner_and_dependent_do_not_overlap() {
    let payload: u32 = kani::any();

    let mut cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

    cell.with_dependent_mut(|owner, dependent| {
        let owner_start = owner as *const Owner as usize;
        let owner_end = owner_start + core::mem::size_of::<Owner>();
        let dep_start = dependent as *const Dependent<'_> as usize;
        let dep_end = dep_start + core::mem::size_of::<Dependent<'_>>();

        assert!(
            owner_end <= dep_start || dep_end <= owner_start,
            "owner and dependent must occupy disjoint memory"
        );

        // Writing through the unique reference must not be visible in the
        // owner.
        dependent.derived = Dependent::expected(owner.payload);
        assert_eq!(owner.payload, payload);
        assert!(owner.is_alive());
    });
}

/// A `not_covariant` dependent exercises the `with_dependent` path only; there
/// is no `borrow_dependent` for it. The macro also swaps in a different owner
/// variance marker, so the generated struct is genuinely a different shape.
#[kani::proof]
fn not_covariant_cell_round_trips() {
    let payload: u32 = kani::any();

    let cell = NotCovariantCell::new(Owner::new(payload), |owner| PlainDependent::build(owner));

    cell.with_dependent(|owner, dependent| {
        assert_eq!(owner.payload, payload);
        assert_eq!(dependent.derived, Dependent::expected(payload));
        assert!(core::ptr::eq(dependent.owner, owner));
    });

    assert_eq!(cell.into_owner().payload, payload);
}
