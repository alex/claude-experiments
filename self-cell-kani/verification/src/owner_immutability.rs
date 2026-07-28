//! Invariant 2 from `unsafe_self_cell.rs`: "owner is NEVER changed again".
//!
//! That invariant is the load-bearing one. Every reference the dependent holds
//! into the owner stays valid *because* the owner is never written to and never
//! moves after construction. These harnesses take a fully symbolic owner —
//! every bit of it nondeterministic — snapshot it, run the public API, and
//! demand the bytes come back identical.
//!
//! The second half deals with the exception: an owner with interior
//! mutability. `into_owner` must run the dependent's destructor *before*
//! `ptr::read`ing the owner out, otherwise a destructor that writes through the
//! self-reference would write into a moved-from value and its effect would be
//! lost. The source calls this out — "Must not read before dropping
//! dependent!!" — and it is exactly the kind of ordering claim worth pinning
//! down.

use core::cell::Cell as StdCell;

use self_cell::self_cell;

// --- A fully symbolic, byte-inspectable owner. ------------------------------

pub const OWNER_BYTES: usize = 8;

#[derive(Debug)]
pub struct ByteOwner {
    pub bytes: [u8; OWNER_BYTES],
}

#[derive(Debug)]
pub struct View<'a> {
    pub owner: &'a ByteOwner,
    pub scratch: u32,
}

self_cell!(
    struct ByteCell {
        owner: ByteOwner,

        #[covariant]
        dependent: View,
    }
);

#[kani::proof]
fn owner_bytes_are_never_modified() {
    let bytes: [u8; OWNER_BYTES] = kani::any();
    let write_a: u32 = kani::any();
    let write_b: u32 = kani::any();

    let mut cell = ByteCell::new(ByteOwner { bytes }, |owner| View {
        owner,
        scratch: 0,
    });

    assert_eq!(cell.borrow_owner().bytes, bytes);

    // Everything the public API lets you do to a live cell.
    cell.with_dependent_mut(|_owner, dependent| dependent.scratch = write_a);
    assert_eq!(cell.borrow_owner().bytes, bytes);

    cell.with_dependent(|owner, dependent| {
        assert_eq!(owner.bytes, bytes);
        assert_eq!(dependent.scratch, write_a);
        assert_eq!(dependent.owner.bytes, bytes);
    });

    cell.with_dependent_mut(|owner, dependent| {
        // Replace the dependent wholesale rather than editing it in place.
        *dependent = View {
            owner,
            scratch: write_b,
        };
    });
    assert_eq!(cell.borrow_owner().bytes, bytes);
    assert_eq!(cell.borrow_dependent().scratch, write_b);

    // ... and the bytes survive being moved out of the cell entirely.
    let recovered = cell.into_owner();
    assert_eq!(recovered.bytes, bytes);
}

/// Same property, read through the dependent's self-reference rather than
/// through the cell, so a divergence between the two would show up.
#[kani::proof]
fn owner_bytes_agree_through_the_self_reference() {
    let bytes: [u8; OWNER_BYTES] = kani::any();

    let cell = ByteCell::new(ByteOwner { bytes }, |owner| View {
        owner,
        scratch: 0,
    });

    cell.with_dependent(|owner, dependent| {
        assert!(core::ptr::eq(dependent.owner, owner));
        for i in 0..OWNER_BYTES {
            assert_eq!(dependent.owner.bytes[i], bytes[i]);
            assert_eq!(owner.bytes[i], bytes[i]);
        }
    });
}

// --- An owner the dependent's destructor writes to. -------------------------

#[derive(Debug)]
pub struct CountingOwner {
    /// Interior mutability, so the dependent can write here through a shared
    /// reference — the one legitimate way an owner changes after construction.
    pub destructor_runs: StdCell<u32>,
    pub payload: u32,
}

#[derive(Debug)]
pub struct WritebackDependent<'a> {
    pub owner: &'a CountingOwner,
}

impl Drop for WritebackDependent<'_> {
    fn drop(&mut self) {
        let previous = self.owner.destructor_runs.get();
        self.owner.destructor_runs.set(previous + 1);
    }
}

self_cell!(
    struct WritebackCell {
        owner: CountingOwner,

        #[covariant]
        dependent: WritebackDependent,
    }
);

/// The ordering claim, stated as an observable: `into_owner` must destroy the
/// dependent before moving the owner out, so the destructor's write is present
/// in the value the caller gets back. If the `ptr::read` happened first, the
/// write would land in the about-to-be-freed allocation and the recovered
/// owner would read `0`.
#[kani::proof]
fn into_owner_sees_the_dependents_writeback() {
    let payload: u32 = kani::any();

    let cell = WritebackCell::new(
        CountingOwner {
            destructor_runs: StdCell::new(0),
            payload,
        },
        |owner| WritebackDependent { owner },
    );

    assert_eq!(cell.borrow_owner().destructor_runs.get(), 0);

    let owner = cell.into_owner();

    assert_eq!(owner.payload, payload);
    assert_eq!(
        owner.destructor_runs.get(),
        1,
        "the dependent's destructor must have run before the owner was moved out"
    );
}

/// The `Drop` path has the same obligation, and additionally must not let the
/// destructor's write happen after the owner is gone.
#[kani::proof]
fn drop_runs_the_writeback_while_the_owner_is_alive() {
    let payload: u32 = kani::any();

    let cell = WritebackCell::new(
        CountingOwner {
            destructor_runs: StdCell::new(0),
            payload,
        },
        |owner| WritebackDependent { owner },
    );

    drop(cell);
}

/// A failed `try_new_or_recover` never builds a dependent, so the recovered
/// owner must show no write-back at all.
#[kani::proof]
fn recovered_owner_shows_no_writeback() {
    let payload: u32 = kani::any();

    let owner = match WritebackCell::try_new_or_recover(
        CountingOwner {
            destructor_runs: StdCell::new(0),
            payload,
        },
        |_| Err::<WritebackDependent<'_>, _>(()),
    ) {
        Ok(_) => unreachable!(),
        Err((owner, ())) => owner,
    };

    assert_eq!(owner.payload, payload);
    assert_eq!(owner.destructor_runs.get(), 0);
}
