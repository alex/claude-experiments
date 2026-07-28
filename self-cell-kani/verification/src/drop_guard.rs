//! The panic-recovery path, reached directly.
//!
//! `OwnerAndCellDropGuard` exists for one reason: if the dependent builder
//! panics after the owner has already been moved into the fresh allocation,
//! something has to destroy that owner and free that allocation. Kani compiles
//! with `panic=abort`, so a panicking builder cannot be used to reach the guard
//! — a panic is a verification failure, not an unwind.
//!
//! So these harnesses reproduce the state the builder leaves behind and run the
//! guard against it: allocate, split with `_field_pointers`, write the owner,
//! arm the guard, drop it. That is byte for byte what `_self_cell_new_body`
//! does up to the point of the panic. What must come out the other side is
//! exactly one owner destructor, zero dependent destructors, and one `dealloc`
//! of the whole `JoinedCell` — not just the owner's share of it.

use core::alloc::Layout;
use core::ptr::NonNull;

use self_cell::unsafe_self_cell::{JoinedCell, OwnerAndCellDropGuard};

use crate::tracking::{self, Dependent, Owner};

/// The lifetime is irrelevant to layout and the dependent is never
/// constructed, so `'static` just names a concrete type to allocate for.
type Cell = JoinedCell<Owner, Dependent<'static>>;

#[kani::proof]
fn guard_cleans_up_a_half_built_cell() {
    let payload: u32 = kani::any();

    unsafe {
        let layout = Layout::new::<Cell>();
        let joined_ptr = NonNull::new(std::alloc::alloc(layout) as *mut Cell).unwrap();

        let (owner_ptr, _dependent_ptr) = Cell::_field_pointers(joined_ptr.as_ptr());

        // The owner is live in its final place; the builder is about to panic.
        owner_ptr.write(Owner::new(payload));
        let guard = OwnerAndCellDropGuard::new(joined_ptr);

        assert_eq!(tracking::owner_drop_count(), 0);

        drop(guard);
    }

    assert_eq!(
        tracking::owner_drop_count(),
        1,
        "the guard must destroy the owner exactly once"
    );
    assert_eq!(
        tracking::dependent_drop_count(),
        0,
        "no dependent was ever constructed, so none may be destroyed"
    );
    // That the allocation was released, and released exactly once, is covered
    // by CBMC's leak and double-free checks (see verify.sh).
}

/// The guard is a plain value: arming and disarming it must be the only thing
/// that decides whether the cleanup happens. Two guards over two allocations
/// must each release their own.
#[kani::proof]
fn two_guards_release_their_own_allocations() {
    let first_payload: u32 = kani::any();
    let second_payload: u32 = kani::any();

    unsafe {
        let layout = Layout::new::<Cell>();

        let first = NonNull::new(std::alloc::alloc(layout) as *mut Cell).unwrap();
        let second = NonNull::new(std::alloc::alloc(layout) as *mut Cell).unwrap();
        assert!(first != second);

        Cell::_field_pointers(first.as_ptr())
            .0
            .write(Owner::new(first_payload));
        Cell::_field_pointers(second.as_ptr())
            .0
            .write(Owner::new(second_payload));

        let first_guard = OwnerAndCellDropGuard::new(first);
        let second_guard = OwnerAndCellDropGuard::new(second);

        drop(first_guard);

        // `second`'s owner must be untouched by `first`'s cleanup.
        assert_eq!(tracking::owner_drop_count(), 1);
        assert!((*second.as_ptr()).owner.is_alive());
        assert_eq!((*second.as_ptr()).owner.payload, second_payload);

        drop(second_guard);
    }

    assert_eq!(tracking::owner_drop_count(), 2);
    assert_eq!(tracking::dependent_drop_count(), 0);
}

/// `mem::forget`ing the guard is how every success path disarms it. Doing so
/// must hand full responsibility back to the caller — the guard must not have
/// pre-emptively freed anything.
#[kani::proof]
fn forgotten_guard_leaves_the_cell_intact() {
    let payload: u32 = kani::any();

    unsafe {
        let layout = Layout::new::<Cell>();
        let joined_ptr = NonNull::new(std::alloc::alloc(layout) as *mut Cell).unwrap();

        let (owner_ptr, dependent_ptr) = Cell::_field_pointers(joined_ptr.as_ptr());
        owner_ptr.write(Owner::new(payload));

        let guard = OwnerAndCellDropGuard::new(joined_ptr);
        core::mem::forget(guard);

        // Everything the guard was protecting is still there and still usable.
        assert!((*owner_ptr).is_alive());
        assert_eq!((*owner_ptr).payload, payload);
        assert_eq!(tracking::owner_drop_count(), 0);

        // Finish what the builder would have finished, then tear it down by
        // hand the way `drop_joined` does.
        dependent_ptr.write(core::mem::transmute::<Dependent<'_>, Dependent<'static>>(
            Dependent::build(&*owner_ptr),
        ));
        core::ptr::drop_in_place(dependent_ptr);
        core::ptr::drop_in_place(owner_ptr);
        std::alloc::dealloc(joined_ptr.as_ptr() as *mut u8, layout);
    }

    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}
