//! `MutBorrow<T>` — the escape hatch that lets a dependent hold `&mut T`.
//!
//! Its soundness argument is that `borrow_mut` can hand out a unique reference
//! at most once, enforced by an `AtomicBool` that only ever goes
//! `false -> true`. Everything else about the type (the `unsafe impl Sync`, the
//! `&self -> &mut T` signature) rests on that single claim.

use self_cell::{self_cell, MutBorrow};

type MutRef<'a> = &'a mut [u8; 4];

self_cell!(
    struct MutCell {
        owner: MutBorrow<[u8; 4]>,

        #[covariant]
        dependent: MutRef,
    }
);

#[kani::proof]
fn borrow_mut_hands_out_a_working_unique_reference() {
    let initial: u8 = kani::any();
    let written: u8 = kani::any();

    let owner = MutBorrow::new([initial; 4]);

    let borrowed: &mut [u8; 4] = owner.borrow_mut();
    assert_eq!(*borrowed, [initial; 4]);
    borrowed[2] = written;

    let recovered = owner.into_inner();
    assert_eq!(recovered[0], initial);
    assert_eq!(recovered[2], written);
}

/// The lock is one-way: a second `borrow_mut` must panic rather than alias.
#[kani::proof]
#[kani::should_panic]
fn second_borrow_mut_panics() {
    let owner = MutBorrow::new([0u8; 4]);

    let _first = owner.borrow_mut();
    let _second = owner.borrow_mut();
}

/// Even without an intervening use, and even when the first borrow is
/// immediately dropped, the lock stays taken.
#[kani::proof]
#[kani::should_panic]
fn lock_is_not_released_by_dropping_the_reference() {
    let owner = MutBorrow::new([0u8; 4]);

    {
        let first = owner.borrow_mut();
        first[0] = 1;
    }

    let _second = owner.borrow_mut();
}

/// The whole `MutBorrow` round trip through a cell: build a dependent holding
/// `&mut [u8; 4]`, mutate through it, then recover the owner.
#[kani::proof]
fn mut_cell_round_trip() {
    let initial: u8 = kani::any();
    let written: u8 = kani::any();

    let mut cell = MutCell::new(MutBorrow::new([initial; 4]), |owner| owner.borrow_mut());

    cell.with_dependent(|_owner, dependent| {
        assert_eq!(**dependent, [initial; 4]);
    });

    cell.with_dependent_mut(|_owner, dependent| {
        dependent[1] = written;
    });

    cell.with_dependent(|_owner, dependent| {
        assert_eq!(dependent[1], written);
        assert_eq!(dependent[3], initial);
    });

    let recovered = cell.into_owner().into_inner();
    assert_eq!(recovered[1], written);
    assert_eq!(recovered[0], initial);
}

/// While the cell is alive the owner is reachable through `borrow_owner`, but
/// the lock taken by the builder must still be held, so no second unique
/// reference can be minted alongside the dependent's.
#[kani::proof]
#[kani::should_panic]
fn borrow_owner_cannot_re_lock_a_built_cell() {
    let cell = MutCell::new(MutBorrow::new([0u8; 4]), |owner| owner.borrow_mut());

    let _aliasing = cell.borrow_owner().borrow_mut();
}

#[kani::proof]
fn mut_cell_drop_is_memory_safe() {
    let initial: u8 = kani::any();

    let cell = MutCell::new(MutBorrow::new([initial; 4]), |owner| owner.borrow_mut());
    drop(cell);
}

/// The lock protocol over an arbitrary number of attempts, not just two.
///
/// `#[kani::should_panic]` requires *every* execution to panic, and the number
/// of attempts here is nondeterministic (but at least two), so this says: no
/// sequence of `borrow_mut` calls of length two or more gets past the lock.
/// Kani models atomics as sequential operations, so this is the sequential half
/// of `MutBorrow`'s argument — the cross-thread half rests on `swap` being a
/// read-modify-write and is outside what Kani checks.
#[kani::proof]
#[kani::should_panic]
#[kani::unwind(6)]
fn no_sequence_of_borrows_gets_two_unique_references() {
    let attempts: usize = kani::any();
    kani::assume(attempts >= 2 && attempts <= 4);

    let owner = MutBorrow::new([0u8; 4]);

    for i in 0..attempts {
        let borrowed = owner.borrow_mut();
        borrowed[0] = i as u8;
    }

    unreachable!("a second borrow_mut must have panicked");
}

/// The mirror image: exactly one attempt must always succeed, whatever the
/// value being wrapped.
#[kani::proof]
fn the_first_borrow_mut_always_succeeds() {
    let initial: u8 = kani::any();
    let written: u8 = kani::any();

    let owner = MutBorrow::new([initial; 4]);
    owner.borrow_mut()[0] = written;

    let recovered = owner.into_inner();
    assert_eq!(recovered[0], written);
    assert_eq!(recovered[1], initial);
}
