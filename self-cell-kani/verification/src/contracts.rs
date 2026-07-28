//! Verification of the function contracts written on `self_cell` itself.
//!
//! The harnesses in the other modules drive the public API and check what comes
//! out. That proves things about the call sequences those harnesses happen to
//! write. Contracts state the obligation on the *function*, and
//! `#[kani::proof_for_contract]` discharges it against an arbitrary input
//! satisfying the precondition — so what is proved no longer depends on how the
//! function was reached.
//!
//! Two kinds of claim are new here and could not be expressed at all before:
//!
//! * **Frame conditions.** `#[kani::modifies()]` with no targets says a
//!   function writes to *nothing*. On `borrow_owner`, `borrow_dependent` and
//!   `borrow_mut` that is the machine-checked form of invariant 4, "the only
//!   access to owner and dependent is as immutable reference". No value-level
//!   harness can state "and it wrote nowhere else".
//! * **Layout obligations at the source.** `JoinedCell::_field_pointers` is
//!   what every other unsafe function is built on. Its contract says the two
//!   pointers land in the allocation, are aligned, and never overlap — stated
//!   once, on the function, rather than re-checked per call site.
//!
//! Because `-Z function-contracts` asserts contracts at call sites by default,
//! every one of the other harnesses now also checks these clauses on every call
//! it makes.

use core::alloc::Layout;
use core::ptr::NonNull;

use self_cell::unsafe_self_cell::{JoinedCell, MutBorrow, SendMutPtr, UnsafeSelfCell};

/// Owner and dependent types with no references in them, so both fields can be
/// filled with `kani::any()` and the accessors get verified over arbitrary cell
/// contents rather than contents some builder produced.
type Cell = JoinedCell<u32, u64>;
type Handle = UnsafeSelfCell<(), u32, u64>;

/// Allocates a `JoinedCell` and fills both fields nondeterministically.
///
/// # Safety
/// The caller must free the returned pointer with `Layout::new::<Cell>()`.
unsafe fn any_initialised_cell() -> NonNull<Cell> {
    let raw = std::alloc::alloc(Layout::new::<Cell>()) as *mut Cell;
    kani::assume(!raw.is_null());

    let (owner_ptr, dependent_ptr) = Cell::_field_pointers(raw);
    owner_ptr.write(kani::any());
    dependent_ptr.write(kani::any());

    NonNull::new(raw).unwrap()
}

unsafe fn free_cell(ptr: NonNull<Cell>) {
    std::alloc::dealloc(ptr.as_ptr() as *mut u8, Layout::new::<Cell>());
}

#[kani::proof_for_contract(UnsafeSelfCell::borrow_owner)]
fn contract_borrow_owner() {
    unsafe {
        let joined = any_initialised_cell();
        let handle = Handle::new(joined.cast::<u8>());

        let owner: &u32 = handle.borrow_owner::<u64>();
        assert_eq!(*owner, (*joined.as_ptr()).owner);

        free_cell(joined);
    }
}

#[kani::proof_for_contract(UnsafeSelfCell::borrow_dependent)]
fn contract_borrow_dependent() {
    unsafe {
        let joined = any_initialised_cell();
        let handle = Handle::new(joined.cast::<u8>());

        let dependent: &u64 = handle.borrow_dependent::<u64>();
        assert_eq!(*dependent, (*joined.as_ptr()).dependent);

        free_cell(joined);
    }
}

#[kani::proof_for_contract(UnsafeSelfCell::borrow_mut)]
fn contract_borrow_mut() {
    unsafe {
        let joined = any_initialised_cell();
        let mut handle = Handle::new(joined.cast::<u8>());

        let owner_before = (*joined.as_ptr()).owner;

        let (owner, dependent) = handle.borrow_mut::<u64>();
        // Writing through the unique reference must not reach the owner. The
        // contract's `modifies()` covers the call itself; this covers the
        // reference it handed out.
        *dependent = kani::any();
        assert_eq!(*owner, owner_before);

        free_cell(joined);
    }
}

#[kani::proof_for_contract(UnsafeSelfCell::new)]
fn contract_unsafe_self_cell_new() {
    unsafe {
        let joined = any_initialised_cell();
        let _handle = Handle::new(joined.cast::<u8>());
        free_cell(joined);
    }
}

// --- `_field_pointers`, over a spread of type shapes. -----------------------
//
// The contract is generic but each proof monomorphises it, so the shapes that
// could plausibly break the layout arithmetic get their own harness: a
// high-alignment owner beside a byte-sized dependent, the mirror image, and a
// zero-sized field on each side.

#[repr(align(16))]
struct BigAlign(u64);

macro_rules! field_pointer_harness {
    ($name:ident, $Owner:ty, $Dependent:ty) => {
        #[kani::proof_for_contract(JoinedCell::_field_pointers)]
        fn $name() {
            type Shape = JoinedCell<$Owner, $Dependent>;

            unsafe {
                let layout = Layout::new::<Shape>();
                kani::assume(layout.size() != 0);

                let raw = std::alloc::alloc(layout) as *mut Shape;
                kani::assume(!raw.is_null());

                let _ = Shape::_field_pointers(raw);

                std::alloc::dealloc(raw as *mut u8, layout);
            }
        }
    };
}

field_pointer_harness!(contract_field_pointers_even, u32, u64);
field_pointer_harness!(contract_field_pointers_big_align_owner, BigAlign, u8);
field_pointer_harness!(contract_field_pointers_big_align_dependent, u8, BigAlign);
field_pointer_harness!(contract_field_pointers_zst_owner, (), u64);
field_pointer_harness!(contract_field_pointers_zst_dependent, u64, ());

// --- The rest. --------------------------------------------------------------

#[kani::proof_for_contract(SendMutPtr::into_non_null)]
fn contract_send_mut_ptr_into_non_null() {
    let mut value: u32 = kani::any();

    // Both a real pointer and a null one must satisfy the contract.
    let raw = if kani::any() {
        &mut value as *mut u32
    } else {
        core::ptr::null_mut()
    };

    let wrapped = SendMutPtr::new(raw);
    let recovered = wrapped.into_non_null();

    assert_eq!(recovered.is_some(), !raw.is_null());
}

#[kani::proof_for_contract(MutBorrow::borrow_mut)]
fn contract_mut_borrow_borrow_mut() {
    let initial: u32 = kani::any();
    let written: u32 = kani::any();

    let cell = MutBorrow::new(initial);

    let borrowed = cell.borrow_mut();
    assert_eq!(*borrowed, initial);
    *borrowed = written;

    assert_eq!(cell.into_inner(), written);
}
