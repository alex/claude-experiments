//! Type shapes that stress the layout arithmetic.
//!
//! Everything the crate does is parameterised on `Owner` and `Dependent`, and
//! the interesting corners are where one of them is degenerate: zero sized,
//! owning its own heap allocation, or borrowed from outside the cell entirely.

use self_cell::self_cell;

use crate::tracking::{self, Owner};

// --- Zero sized types. ------------------------------------------------------

#[derive(Debug)]
pub struct ZeroSizedDependent<'a>(core::marker::PhantomData<&'a ()>);

#[derive(Debug)]
pub struct SizedDependent<'a> {
    pub owner: &'a (),
    pub value: u32,
}

self_cell!(
    /// A zero sized owner is fine as long as *something* in the cell has size.
    struct ZstOwnerCell {
        owner: (),

        #[covariant]
        dependent: SizedDependent,
    }
);

self_cell!(
    /// ... and likewise a zero sized dependent.
    struct ZstDependentCell {
        owner: Owner,

        #[covariant]
        dependent: ZeroSizedDependent,
    }
);

self_cell!(
    /// Both zero sized, so `JoinedCell` is zero sized too. `alloc` with a
    /// zero-size layout is undefined behaviour, so the macro asserts against it
    /// — see `both_zero_sized_is_rejected`.
    struct FullyZstCell {
        owner: (),

        #[covariant]
        dependent: ZeroSizedDependent,
    }
);

#[kani::proof]
fn zero_sized_owner_works() {
    let value: u32 = kani::any();

    let cell = ZstOwnerCell::new((), |owner| SizedDependent { owner, value });

    assert_eq!(cell.borrow_dependent().value, value);
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));

    cell.into_owner();
}

#[kani::proof]
fn zero_sized_dependent_works() {
    let payload: u32 = kani::any();

    let cell = ZstDependentCell::new(Owner::new(payload), |_| {
        ZeroSizedDependent(core::marker::PhantomData)
    });

    assert_eq!(cell.borrow_owner().payload, payload);

    let owner = cell.into_owner();
    assert_eq!(owner.payload, payload);
    assert!(owner.is_alive());
    drop(owner);

    assert_eq!(tracking::owner_drop_count(), 1);
}

/// A documented limitation rather than a defect: when owner *and* dependent are
/// both zero sized there is nothing to allocate, and `alloc` with a zero-size
/// layout would be UB. The macro chooses a panic. This harness pins that
/// behaviour down — it is a safe-code panic, not unsoundness, but it is also
/// not something the crate's documentation mentions.
#[kani::proof]
#[kani::should_panic]
fn both_zero_sized_is_rejected() {
    let _cell = FullyZstCell::new((), |_| ZeroSizedDependent(core::marker::PhantomData));
}

// --- An owner that owns its own allocation. ---------------------------------

#[derive(Debug)]
pub struct BoxOwner {
    pub inner: Box<u32>,
}

#[derive(Debug)]
pub struct BoxDependent<'a> {
    pub owner: &'a BoxOwner,
    pub doubled: u32,
}

self_cell!(
    struct BoxCell {
        owner: BoxOwner,

        #[covariant]
        dependent: BoxDependent,
    }
);

/// `into_owner` `ptr::read`s the owner out of the `JoinedCell` and then frees
/// that cell. If the read were a copy rather than a move — or if the cell were
/// freed with the owner still logically in it — the owner's *own* allocation
/// would be double freed or leaked. Neither must happen.
#[kani::proof]
fn owner_with_its_own_allocation_survives_into_owner() {
    let value: u32 = kani::any();

    let cell = BoxCell::new(
        BoxOwner {
            inner: Box::new(value),
        },
        |owner| BoxDependent {
            owner,
            doubled: owner.inner.wrapping_mul(2),
        },
    );

    assert_eq!(cell.borrow_dependent().doubled, value.wrapping_mul(2));
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));

    let owner = cell.into_owner();
    assert_eq!(*owner.inner, value);

    // The box outlives the cell it was stored in.
    let recovered = *owner.inner;
    drop(owner);
    assert_eq!(recovered, value);
}

#[kani::proof]
fn owner_with_its_own_allocation_survives_drop() {
    let value: u32 = kani::any();

    let cell = BoxCell::new(
        BoxOwner {
            inner: Box::new(value),
        },
        |owner| BoxDependent {
            owner,
            doubled: owner.inner.wrapping_mul(2),
        },
    );

    drop(cell);
}

// --- An owner that is itself a borrow: nested cells. ------------------------

#[derive(Debug)]
pub struct BorrowedDependent<'a> {
    pub owner: &'a Owner,
    pub derived: u32,
}

self_cell!(
    /// The macro's optional owner lifetime. This also swaps in a different
    /// `_covariant_owner_marker`, so the generated struct has an extra
    /// `PhantomData` field that `#[repr(transparent)]` has to tolerate.
    struct ChildCell<'a> {
        owner: &'a Owner,

        #[covariant]
        dependent: BorrowedDependent,
    }
);

#[kani::proof]
fn cell_over_a_borrowed_owner() {
    let payload: u32 = kani::any();

    let outer = Owner::new(payload);

    {
        let cell = ChildCell::new(&outer, |owner| BorrowedDependent {
            owner,
            derived: owner.payload.wrapping_mul(3).wrapping_add(1),
        });

        assert_eq!(cell.borrow_owner().payload, payload);
        assert_eq!(
            cell.borrow_dependent().derived,
            payload.wrapping_mul(3).wrapping_add(1)
        );
        // The dependent points at the *outer* owner, not at a copy inside the
        // cell: the cell only stores the reference.
        assert!(core::ptr::eq(cell.borrow_dependent().owner, &outer));

        // Dropping the cell must not drop the borrowed owner.
        drop(cell);
        assert_eq!(tracking::owner_drop_count(), 0);
    }

    assert!(outer.is_alive());
    assert_eq!(outer.payload, payload);
    drop(outer);
    assert_eq!(tracking::owner_drop_count(), 1);
}

#[kani::proof]
fn borrowed_owner_cell_into_owner() {
    let payload: u32 = kani::any();

    let outer = Owner::new(payload);

    let cell = ChildCell::new(&outer, |owner| BorrowedDependent {
        owner,
        derived: owner.payload,
    });

    let recovered: &Owner = cell.into_owner();
    assert!(core::ptr::eq(recovered, &outer));
    assert!(recovered.is_alive());
    assert_eq!(tracking::owner_drop_count(), 0);

    drop(outer);
    assert_eq!(tracking::owner_drop_count(), 1);
}

// --- Neither side has a destructor. -----------------------------------------

#[derive(Debug)]
pub struct PodOwner {
    pub bytes: [u8; 3],
}

#[derive(Debug)]
pub struct PodDependent<'a> {
    pub owner: &'a PodOwner,
    pub sum: u16,
}

self_cell!(
    struct PodCell {
        owner: PodOwner,

        #[covariant]
        dependent: PodDependent,
    }
);

/// With `needs_drop` false for both fields the compiler elides the
/// `drop_in_place` calls entirely, leaving only the deallocation. The
/// allocation still has to be released exactly once.
#[kani::proof]
fn cell_without_destructors() {
    let bytes: [u8; 3] = kani::any();

    let cell = PodCell::new(PodOwner { bytes }, |owner| PodDependent {
        owner,
        sum: owner.bytes.iter().map(|b| *b as u16).sum(),
    });

    let expected: u16 = bytes.iter().map(|b| *b as u16).sum();
    assert_eq!(cell.borrow_dependent().sum, expected);
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));
    assert_eq!(cell.borrow_owner().bytes, bytes);

    drop(cell);
}

// --- A dependent that owns its own allocation. ------------------------------

#[derive(Debug)]
pub struct BoxedDependent<'a> {
    pub owner: &'a Owner,
    pub scratch: Box<u32>,
}

self_cell!(
    struct BoxedDependentCell {
        owner: Owner,

        #[covariant]
        dependent: BoxedDependent,
    }
);

/// The dependent's own heap allocation has to be released exactly once, by its
/// destructor, before the `JoinedCell` that holds it is freed — on both the
/// `Drop` path and the `into_owner` path.
#[kani::proof]
fn dependent_with_its_own_allocation() {
    let payload: u32 = kani::any();
    let consume: bool = kani::any();

    let cell = BoxedDependentCell::new(Owner::new(payload), |owner| BoxedDependent {
        owner,
        scratch: Box::new(owner.payload),
    });

    assert_eq!(*cell.borrow_dependent().scratch, payload);

    if consume {
        let owner = cell.into_owner();
        assert_eq!(owner.payload, payload);
        assert!(owner.is_alive());
        drop(owner);
    } else {
        drop(cell);
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}
