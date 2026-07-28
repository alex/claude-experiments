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

/// The lock never resets, however many times you knock.
///
/// Note the shape of every `should_panic` harness in this file: no
/// nondeterminism on the path to the panic. That is deliberate.
/// `#[kani::should_panic]` succeeds if *at least one* execution panics, not if
/// all of them do — a harness that panicked only on `kani::any() == 7` also
/// passes. So a `should_panic` harness only pins down "this always panics" when
/// it has a single path, which is why the attempt count here is a constant
/// rather than a symbolic value.
///
/// Kani also models atomics as sequential operations, so this is the sequential
/// half of `MutBorrow`'s argument. The cross-thread half rests on `swap` being
/// a read-modify-write and is outside what Kani checks.
#[kani::proof]
#[kani::should_panic]
fn lock_stays_taken_across_repeated_attempts() {
    let owner = MutBorrow::new([0u8; 4]);

    let first = owner.borrow_mut();
    first[0] = 1;

    // Each of these must panic; the first one to run does.
    let _second = owner.borrow_mut();
    let _third = owner.borrow_mut();
    let _fourth = owner.borrow_mut();
}

/// The mirror image, and the one direction that can be stated universally:
/// whatever the wrapped value, the first attempt succeeds and hands back a
/// reference that really writes through to it.
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
