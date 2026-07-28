//! Instrumented owner / dependent types used by the proof harnesses.
//!
//! Kani verifies one harness at a time as a standalone, single threaded
//! program, so plain global counters are a sound way to observe drop events.
//! They are `Atomic*` purely so we can mutate them from `&self` without
//! `static mut`.

use core::sync::atomic::{AtomicUsize, Ordering};

/// Monotonic clock; every recorded event takes the next tick. Ticks start at 1
/// so that `0` unambiguously means "this never happened".
static CLOCK: AtomicUsize = AtomicUsize::new(0);

static OWNER_DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
static OWNER_DROP_AT: AtomicUsize = AtomicUsize::new(0);
static DEPENDENT_DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
static DEPENDENT_DROP_AT: AtomicUsize = AtomicUsize::new(0);

fn tick() -> usize {
    CLOCK.fetch_add(1, Ordering::Relaxed) + 1
}

pub fn owner_drop_count() -> usize {
    OWNER_DROP_COUNT.load(Ordering::Relaxed)
}

pub fn owner_dropped_at() -> usize {
    OWNER_DROP_AT.load(Ordering::Relaxed)
}

pub fn dependent_drop_count() -> usize {
    DEPENDENT_DROP_COUNT.load(Ordering::Relaxed)
}

pub fn dependent_dropped_at() -> usize {
    DEPENDENT_DROP_AT.load(Ordering::Relaxed)
}

/// Lets dependent types defined outside this module record their destruction
/// the same way `Dependent` does.
pub fn note_dependent_drop() {
    DEPENDENT_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
    DEPENDENT_DROP_AT.store(tick(), Ordering::Relaxed);
}

/// Written into `Owner::canary` on construction.
const ALIVE: u64 = 0x5e1f_ce11_a11e_0000;
/// Written into `Owner::canary` by `Owner::drop`.
const DEAD: u64 = 0xdead_dead_dead_dead;

/// Owner type that records its own destruction, both as a global event and as
/// an in-band poison value.
///
/// The poison value is what makes wrong drop *ordering* observable: if the
/// owner were destroyed before the dependent, the dependent's destructor would
/// read `DEAD`. Reading the field at all is also what makes a premature
/// *deallocation* observable, since Kani reports the dereference of a freed
/// pointer.
#[derive(Debug)]
pub struct Owner {
    pub payload: u32,
    canary: u64,
}

impl Owner {
    pub fn new(payload: u32) -> Self {
        Self {
            payload,
            canary: ALIVE,
        }
    }

    pub fn is_alive(&self) -> bool {
        self.canary == ALIVE
    }
}

impl Drop for Owner {
    fn drop(&mut self) {
        OWNER_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        OWNER_DROP_AT.store(tick(), Ordering::Relaxed);
        self.canary = DEAD;
    }
}

/// Dependent type that borrows the owner, i.e. the self-reference whose
/// validity is the entire point of the crate.
#[derive(Debug)]
pub struct Dependent<'a> {
    pub owner: &'a Owner,
    /// Function of `owner.payload`; the destructor re-checks it, so this field
    /// must be left consistent.
    pub derived: u32,
    /// Free real estate for harnesses that just want to write somewhere.
    pub scratch: u32,
}

impl<'a> Dependent<'a> {
    pub fn build(owner: &'a Owner) -> Self {
        Self {
            owner,
            derived: owner.payload.wrapping_mul(3).wrapping_add(1),
            scratch: 0,
        }
    }

    /// What `build` should have computed for `payload`.
    pub fn expected(payload: u32) -> u32 {
        payload.wrapping_mul(3).wrapping_add(1)
    }
}

impl Drop for Dependent<'_> {
    fn drop(&mut self) {
        DEPENDENT_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        DEPENDENT_DROP_AT.store(tick(), Ordering::Relaxed);

        // The self-reference must still be valid here. A premature `dealloc`
        // makes this dereference a use-after-free (caught by Kani's pointer
        // checks); dropping the owner first makes the canary read `DEAD`.
        assert!(
            self.owner.is_alive(),
            "dependent outlived its owner's destructor"
        );
        assert_eq!(self.derived, Dependent::expected(self.owner.payload));
    }
}

/// A dependent with no `Drop` impl, for harnesses where a destructor would
/// mask the property under test.
#[derive(Debug)]
pub struct PlainDependent<'a> {
    pub owner: &'a Owner,
    pub derived: u32,
}

impl<'a> PlainDependent<'a> {
    pub fn build(owner: &'a Owner) -> Self {
        Self {
            owner,
            derived: owner.payload.wrapping_mul(3).wrapping_add(1),
        }
    }
}
