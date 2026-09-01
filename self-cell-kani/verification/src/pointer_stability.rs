//! Layout obligations.
//!
//! `self_cell` allocates `Layout::new::<JoinedCell<Owner, Dependent>>()` bytes,
//! splits them with `addr_of_mut!`, and then repeatedly casts a `NonNull<u8>`
//! back to `JoinedCell<Owner, Dependent>` from call sites that only know
//! `Dependent` up to its lifetime. These harnesses pin down the consequences:
//! addresses stay put across moves, both fields land properly aligned inside
//! the allocation, and the generated struct really is pointer sized.

use self_cell::self_cell;

// --- A high-alignment owner next to a byte-aligned dependent. ---------------

#[repr(align(16))]
#[derive(Debug)]
pub struct AlignedOwner {
    pub value: u64,
}

#[derive(Debug)]
pub struct SmallDependent<'a> {
    pub owner: &'a AlignedOwner,
    pub tag: u8,
}

self_cell!(
    struct AlignedOwnerCell {
        owner: AlignedOwner,

        #[covariant]
        dependent: SmallDependent,
    }
);

// --- ... and the mirror image. ----------------------------------------------

#[derive(Debug)]
pub struct ByteOwner {
    pub value: u8,
}

#[repr(align(32))]
#[derive(Debug)]
pub struct AlignedDependent<'a> {
    pub owner: &'a ByteOwner,
    pub value: u64,
}

self_cell!(
    struct AlignedDependentCell {
        owner: ByteOwner,

        #[covariant]
        dependent: AlignedDependent,
    }
);

fn is_aligned_for<T>(ptr: *const T) -> bool {
    (ptr as usize) % core::mem::align_of::<T>() == 0
}

#[kani::proof]
fn addresses_are_stable_across_moves() {
    let value: u64 = kani::any();

    let cell = AlignedOwnerCell::new(AlignedOwner { value }, |owner| SmallDependent {
        owner,
        tag: 7,
    });

    // Addresses are kept as integers so they outlive the borrow of `cell`.
    let owner_addr = cell.borrow_owner() as *const AlignedOwner as usize;
    let dependent_addr = cell.with_dependent(|_, dependent| dependent as *const _ as usize);

    // Move it around: onto the stack, into a box, back out, through a tuple.
    let moved = cell;
    let boxed = Box::new(moved);
    let (unboxed, _padding) = (*boxed, 0u128);

    assert_eq!(
        unboxed.borrow_owner() as *const AlignedOwner as usize,
        owner_addr
    );
    assert_eq!(
        unboxed.with_dependent(|_, dependent| dependent as *const _ as usize),
        dependent_addr
    );
    assert_eq!(unboxed.borrow_owner().value, value);
    assert_eq!(unboxed.borrow_dependent().tag, 7);
}

#[kani::proof]
fn fields_are_aligned_and_disjoint_high_align_owner() {
    let value: u64 = kani::any();
    let tag: u8 = kani::any();

    let mut cell = AlignedOwnerCell::new(AlignedOwner { value }, |owner| SmallDependent {
        owner,
        tag,
    });

    cell.with_dependent_mut(|owner, dependent| {
        let owner_ptr = owner as *const AlignedOwner;
        let dep_ptr = dependent as *const SmallDependent<'_>;

        assert!(is_aligned_for(owner_ptr));
        assert!(is_aligned_for(dep_ptr));

        let owner_start = owner_ptr as usize;
        let owner_end = owner_start + core::mem::size_of::<AlignedOwner>();
        let dep_start = dep_ptr as usize;
        let dep_end = dep_start + core::mem::size_of::<SmallDependent<'_>>();
        assert!(owner_end <= dep_start || dep_end <= owner_start);

        assert_eq!(owner.value, value);
        assert_eq!(dependent.tag, tag);
        assert!(core::ptr::eq(dependent.owner, owner));
    });
}

#[kani::proof]
fn fields_are_aligned_and_disjoint_high_align_dependent() {
    let value: u8 = kani::any();
    let derived: u64 = kani::any();

    let mut cell = AlignedDependentCell::new(ByteOwner { value }, |owner| AlignedDependent {
        owner,
        value: derived,
    });

    cell.with_dependent_mut(|owner, dependent| {
        let owner_ptr = owner as *const ByteOwner;
        let dep_ptr = dependent as *const AlignedDependent<'_>;

        assert!(is_aligned_for(owner_ptr));
        assert!(is_aligned_for(dep_ptr));

        let owner_start = owner_ptr as usize;
        let owner_end = owner_start + core::mem::size_of::<ByteOwner>();
        let dep_start = dep_ptr as usize;
        let dep_end = dep_start + core::mem::size_of::<AlignedDependent<'_>>();
        assert!(owner_end <= dep_start || dep_end <= owner_start);

        assert_eq!(owner.value, value);
        assert_eq!(dependent.value, derived);
        assert!(core::ptr::eq(dependent.owner, owner));
    });

    assert_eq!(cell.into_owner().value, value);
}

/// The generated struct is `#[repr(transparent)]` over an `UnsafeSelfCell`,
/// which is in turn a `NonNull<u8>` plus `PhantomData`. `into_owner`
/// `transmute`s between the two, which is only sound if the layouts match, and
/// the `NonNull` niche should survive as well.
#[kani::proof]
fn generated_struct_is_a_pointer_with_a_niche() {
    use core::mem::{align_of, size_of};

    assert_eq!(size_of::<AlignedOwnerCell>(), size_of::<*const u8>());
    assert_eq!(align_of::<AlignedOwnerCell>(), align_of::<*const u8>());
    assert_eq!(
        size_of::<Option<AlignedOwnerCell>>(),
        size_of::<AlignedOwnerCell>(),
        "the NonNull niche must survive, otherwise the transmute in \
         into_owner would be reinterpreting a differently sized value"
    );

    assert_eq!(size_of::<AlignedDependentCell>(), size_of::<*const u8>());
}
