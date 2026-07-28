//! Quantifying over the callbacks, not just picking one.
//!
//! Every entry point in `self_cell` takes a user callback: `new`, `try_new` and
//! `try_new_or_recover` take a dependent builder, `with_dependent` and
//! `with_dependent_mut` take a visitor. A harness that passes one concrete
//! closure proves the property for that closure. What we want is the property
//! for *any* closure a user could write.
//!
//! Kani cannot quantify over code — it model-checks one monomorphic program.
//! But the quantification can be pushed down to values, because `self_cell`
//! never inspects the callback: it calls it, and does the same thing with
//! whatever comes back. So "for all builders" reduces to "for all things a
//! builder could return, and all ways it could get there", and *that* is
//! symbolic:
//!
//! * **Return value.** The scalar fields of the dependent are `kani::any()`.
//! * **The self-reference.** A builder cannot conjure a `&'a Owner` — the only
//!   one in scope is its argument. So the reachable choices are exactly: don't
//!   reference the owner, reference the whole owner, or reference some part of
//!   it. `Anchor` enumerates all three and the choice is symbolic.
//! * **Control flow.** Whether the fallible builders return `Ok` or `Err`, and
//!   which error, is symbolic.
//! * **Side effects.** The only state a builder can touch is the owner it was
//!   handed, and only through interior mutability. `MutatingOwner` gives it
//!   some, and whether and how much it writes is symbolic.
//! * **Visitors.** `with_dependent_mut` may leave the dependent alone, edit it,
//!   or replace it wholesale (dropping the old one). Which, and with what, is
//!   symbolic.
//!
//! What stays outside: a builder that *panics* (Kani compiles with
//! `panic=abort`, so panics are failures rather than unwinds — see `drop_guard`
//! and `async_builder::cancelling_construction_cleans_up` for how that path is
//! covered instead), and dependent types other than the ones instantiated here.

use core::cell::Cell as StdCell;

use self_cell::self_cell;

use crate::tracking::{self, Owner};

/// Every way a builder could anchor its result to the owner it was given.
#[derive(Debug)]
pub enum Anchor<'a> {
    /// The builder ignored the owner.
    Detached,
    /// The builder kept the owner itself.
    Whole(&'a Owner),
    /// The builder kept a reference into the owner.
    Field(&'a u32),
}

/// A dependent whose entire contents are nondeterministic, subject only to the
/// constraints the type system puts on a real builder.
#[derive(Debug)]
pub struct AnyDependent<'a> {
    pub anchor: Anchor<'a>,
    pub scalar: u32,
    pub wide: u64,
    pub bytes: [u8; 3],
}

impl Drop for AnyDependent<'_> {
    fn drop(&mut self) {
        tracking::note_dependent_drop();

        // Whatever the builder anchored to must still be readable here.
        match self.anchor {
            Anchor::Detached => {}
            Anchor::Whole(owner) => assert!(
                owner.is_alive(),
                "dependent outlived its owner's destructor"
            ),
            Anchor::Field(payload) => {
                // Reading a freed allocation is a Kani pointer failure.
                let _ = *payload;
            }
        }
    }
}

fn any_anchor(owner: &Owner) -> Anchor<'_> {
    let choice: u8 = kani::any();
    kani::assume(choice < 3);

    match choice {
        0 => Anchor::Detached,
        1 => Anchor::Whole(owner),
        _ => Anchor::Field(&owner.payload),
    }
}

/// Stands for an arbitrary dependent builder.
fn any_dependent(owner: &Owner) -> AnyDependent<'_> {
    // A real builder may read the owner first.
    assert!(owner.is_alive());

    AnyDependent {
        anchor: any_anchor(owner),
        scalar: kani::any(),
        wide: kani::any(),
        bytes: kani::any(),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AnyError(u32);

/// Stands for an arbitrary fallible dependent builder.
fn any_fallible_dependent(owner: &Owner) -> Result<AnyDependent<'_>, AnyError> {
    if kani::any() {
        Err(AnyError(kani::any()))
    } else {
        Ok(any_dependent(owner))
    }
}

/// Checks the parts of the cell's state that must hold no matter what the
/// builder chose.
fn check(cell: &AnyCell, payload: u32, owner_addr: usize) {
    assert!(cell.borrow_owner().is_alive());
    assert_eq!(cell.borrow_owner().payload, payload);
    assert_eq!(cell.borrow_owner() as *const Owner as usize, owner_addr);

    match cell.borrow_dependent().anchor {
        Anchor::Detached => {}
        Anchor::Whole(owner) => {
            assert!(core::ptr::eq(owner, cell.borrow_owner()));
            assert_eq!(owner.payload, payload);
        }
        Anchor::Field(field) => {
            assert!(core::ptr::eq(field, &cell.borrow_owner().payload));
            assert_eq!(*field, payload);
        }
    }
}

self_cell!(
    struct AnyCell {
        owner: Owner,

        #[covariant]
        dependent: AnyDependent,
    }
);

#[kani::proof]
fn new_with_an_arbitrary_builder() {
    let payload: u32 = kani::any();

    let cell = AnyCell::new(Owner::new(payload), any_dependent);
    let owner_addr = cell.borrow_owner() as *const Owner as usize;

    check(&cell, payload, owner_addr);

    drop(cell);

    assert_eq!(tracking::owner_drop_count(), 1);
    assert_eq!(tracking::dependent_drop_count(), 1);
}

#[kani::proof]
fn into_owner_with_an_arbitrary_builder() {
    let payload: u32 = kani::any();

    let cell = AnyCell::new(Owner::new(payload), any_dependent);
    let owner = cell.into_owner();

    assert_eq!(tracking::dependent_drop_count(), 1);
    assert_eq!(tracking::owner_drop_count(), 0);
    assert_eq!(owner.payload, payload);
    assert!(owner.is_alive());
}

#[kani::proof]
fn try_new_with_an_arbitrary_fallible_builder() {
    let payload: u32 = kani::any();

    match AnyCell::try_new(Owner::new(payload), any_fallible_dependent) {
        Ok(cell) => {
            let owner_addr = cell.borrow_owner() as *const Owner as usize;
            check(&cell, payload, owner_addr);
            drop(cell);
            assert_eq!(tracking::dependent_drop_count(), 1);
        }
        Err(AnyError(_)) => {
            assert_eq!(tracking::dependent_drop_count(), 0);
        }
    }

    // Either way the owner is consumed exactly once.
    assert_eq!(tracking::owner_drop_count(), 1);
}

#[kani::proof]
fn try_new_or_recover_with_an_arbitrary_fallible_builder() {
    let payload: u32 = kani::any();

    match AnyCell::try_new_or_recover(Owner::new(payload), any_fallible_dependent) {
        Ok(cell) => {
            let owner_addr = cell.borrow_owner() as *const Owner as usize;
            check(&cell, payload, owner_addr);
            drop(cell);
            assert_eq!(tracking::dependent_drop_count(), 1);
        }
        Err((owner, AnyError(_))) => {
            assert_eq!(
                tracking::owner_drop_count(),
                0,
                "the recovered owner must not have been dropped in place"
            );
            assert!(owner.is_alive());
            assert_eq!(owner.payload, payload);
            assert_eq!(tracking::dependent_drop_count(), 0);
            drop(owner);
        }
    }

    assert_eq!(tracking::owner_drop_count(), 1);
}

/// Arbitrary *visitors*, on top of an arbitrary builder. The `with_dependent_mut`
/// callback may do nothing, edit the dependent, or replace it entirely — which
/// runs the old dependent's destructor while the cell is still live.
#[kani::proof]
#[kani::unwind(4)]
fn arbitrary_visitors_over_an_arbitrary_cell() {
    let payload: u32 = kani::any();

    let mut cell = AnyCell::new(Owner::new(payload), any_dependent);
    let owner_addr = cell.borrow_owner() as *const Owner as usize;

    for _ in 0..2 {
        let which: u8 = kani::any();
        kani::assume(which < 4);

        match which {
            0 => {
                cell.with_dependent(|owner, dependent| {
                    assert!(owner.is_alive());
                    match dependent.anchor {
                        Anchor::Detached => {}
                        Anchor::Whole(anchored) => assert!(core::ptr::eq(anchored, owner)),
                        Anchor::Field(field) => assert!(core::ptr::eq(field, &owner.payload)),
                    }
                });
            }
            1 => {
                cell.with_dependent_mut(|_owner, dependent| {
                    dependent.scalar = kani::any();
                    dependent.wide = kani::any();
                    dependent.bytes = kani::any();
                });
            }
            2 => {
                // Replace the dependent wholesale. The assignment drops the old
                // one in place, so its destructor runs against a live owner
                // inside a live cell.
                let before = tracking::dependent_drop_count();
                cell.with_dependent_mut(|owner, dependent| {
                    *dependent = any_dependent(owner);
                });
                assert_eq!(tracking::dependent_drop_count(), before + 1);
            }
            _ => {
                // A visitor may hand back a reference into the dependent; it
                // has to stay valid after the visitor returns.
                let escaped: &u32 = cell.with_dependent(|_owner, dependent| &dependent.scalar);
                let seen = *escaped;
                assert_eq!(seen, cell.borrow_dependent().scalar);
            }
        }

        check(&cell, payload, owner_addr);
    }

    drop(cell);
    assert_eq!(tracking::owner_drop_count(), 1);
}

// --- A builder that writes to the owner it was handed. ----------------------

#[derive(Debug)]
pub struct MutatingOwner {
    pub writes: StdCell<u32>,
    pub payload: u32,
}

#[derive(Debug)]
pub struct Witness<'a> {
    pub owner: &'a MutatingOwner,
}

self_cell!(
    struct MutatingCell {
        owner: MutatingOwner,

        #[covariant]
        dependent: Witness,
    }
);

/// Interior mutability is the one way a builder can change the owner, and it is
/// allowed to do so an arbitrary number of times before returning. None of it
/// may disturb where the owner lives or what the cell does with it afterwards.
#[kani::proof]
#[kani::unwind(4)]
fn builder_that_writes_to_the_owner() {
    let payload: u32 = kani::any();
    let writes: u32 = kani::any();
    kani::assume(writes <= 2);

    let cell = MutatingCell::new(
        MutatingOwner {
            writes: StdCell::new(0),
            payload,
        },
        |owner| {
            for _ in 0..writes {
                owner.writes.set(owner.writes.get() + 1);
            }
            Witness { owner }
        },
    );

    assert_eq!(cell.borrow_owner().writes.get(), writes);
    assert_eq!(cell.borrow_owner().payload, payload);
    assert!(core::ptr::eq(cell.borrow_dependent().owner, cell.borrow_owner()));

    let recovered = cell.into_owner();
    assert_eq!(recovered.writes.get(), writes);
    assert_eq!(recovered.payload, payload);
}

/// Reachability evidence for the harnesses above.
///
/// The claim "this covers every builder outcome" is only worth something if
/// Kani actually explores every outcome — a stray `assume` that pruned one
/// would leave the other harnesses passing for the wrong reason. `kani::cover!`
/// asserts the opposite of an assertion: each of these must be *satisfiable*.
#[kani::proof]
fn every_builder_outcome_is_reachable() {
    let payload: u32 = kani::any();

    match AnyCell::try_new_or_recover(Owner::new(payload), any_fallible_dependent) {
        Ok(cell) => {
            kani::cover!(true, "builder succeeded");
            match cell.borrow_dependent().anchor {
                Anchor::Detached => kani::cover!(true, "dependent ignores the owner"),
                Anchor::Whole(_) => kani::cover!(true, "dependent holds the whole owner"),
                Anchor::Field(_) => kani::cover!(true, "dependent holds a field of the owner"),
            }
            kani::cover!(cell.borrow_dependent().scalar == 0, "scalar can be 0");
            kani::cover!(cell.borrow_dependent().scalar == u32::MAX, "scalar can be MAX");
            drop(cell);
        }
        Err((owner, AnyError(code))) => {
            kani::cover!(true, "builder failed");
            kani::cover!(code == 0, "error code can be 0");
            kani::cover!(code != 0, "error code can be non-zero");
            drop(owner);
        }
    }
}
