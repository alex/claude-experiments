//! Arbitrary sequences of public API calls.
//!
//! The other harnesses each fix one call sequence. This one leaves the
//! sequence itself nondeterministic: Kani explores *every* interleaving of the
//! public operations up to a bounded length, checking after each step that the
//! cell's invariants still hold. If some particular order of `borrow_owner`,
//! `borrow_dependent`, `with_dependent` and `with_dependent_mut` corrupted the
//! cell, this is where it would surface.

use self_cell::self_cell;

use crate::tracking::{self, Dependent, Owner};

self_cell!(
    struct Cell {
        owner: Owner,

        #[covariant]
        dependent: Dependent,
    }
);

const OPS: usize = 4;

fn check(cell: &Cell, payload: u32) {
    assert!(cell.borrow_owner().is_alive());
    assert_eq!(cell.borrow_owner().payload, payload);
    assert_eq!(cell.borrow_dependent().derived, Dependent::expected(payload));
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));
}

#[kani::proof]
#[kani::unwind(6)]
fn any_sequence_of_operations_preserves_the_invariants() {
    let payload: u32 = kani::any();

    let mut cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));
    let base = cell.borrow_owner() as *const Owner as usize;

    let mut scratch: u32 = 0;

    for _ in 0..OPS {
        let op: u8 = kani::any();
        kani::assume(op < 5);

        match op {
            0 => {
                let owner = cell.borrow_owner();
                assert_eq!(owner as *const Owner as usize, base);
            }
            1 => {
                let dependent = cell.borrow_dependent();
                assert_eq!(dependent.scratch, scratch);
            }
            2 => {
                cell.with_dependent(|owner, dependent| {
                    assert!(core::ptr::eq(dependent.owner, owner));
                    assert_eq!(dependent.scratch, scratch);
                });
            }
            3 => {
                let written: u32 = kani::any();
                cell.with_dependent_mut(|_owner, dependent| {
                    dependent.scratch = written;
                });
                scratch = written;
            }
            _ => {
                // Read the owner through the dependent's self-reference rather
                // than through the cell.
                let via_dependent = cell.borrow_dependent().owner.payload;
                assert_eq!(via_dependent, payload);
            }
        }

        check(&cell, payload);
    }

    // However the sequence went, teardown is still balanced.
    drop(cell);
    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}

/// Same idea, but the sequence ends in a nondeterministically chosen teardown:
/// either `Drop` or `into_owner`. The two have completely different
/// implementations and must agree on the accounting.
#[kani::proof]
#[kani::unwind(5)]
fn any_sequence_then_either_teardown() {
    let payload: u32 = kani::any();
    let consume: bool = kani::any();

    let mut cell = Cell::new(Owner::new(payload), |owner| Dependent::build(owner));

    for _ in 0..3 {
        let op: u8 = kani::any();
        kani::assume(op < 2);

        if op == 0 {
            check(&cell, payload);
        } else {
            let written: u32 = kani::any();
            cell.with_dependent_mut(|_owner, dependent| dependent.scratch = written);
            assert_eq!(cell.borrow_dependent().scratch, written);
        }
    }

    if consume {
        let owner = cell.into_owner();
        assert_eq!(tracking::dependent_drop_count(), 1);
        assert_eq!(tracking::owner_drop_count(), 0);
        assert_eq!(owner.payload, payload);
        assert!(owner.is_alive());
        drop(owner);
    } else {
        drop(cell);
    }

    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}
