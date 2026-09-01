#!/usr/bin/env python3
"""Regenerate the mutant patches in this directory from the current source.

Each mutant injects one bug into self_cell. The patches are what `run.sh`
applies, but they are derived artefacts: keeping the mutations here as
search-and-replace pairs means they survive edits to the surrounding code,
which a hand-maintained patch would not.

Usage: ./generate.py
"""

import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
CRATE = HERE.parent.parent
SOURCES = ["src/lib.rs", "src/unsafe_self_cell.rs"]

# name -> list of (file, find, replace)
MUTATIONS = {
    # --- Value-level bugs: caught by the behavioural harnesses. -------------
    "m1_drop_order": [(
        "src/unsafe_self_cell.rs",
        """        // Also used in case drop_in_place(...dependent) fails
        let _guard = OwnerAndCellDropGuard { joined_ptr };

        // IMPORTANT dependent must be dropped before owner.
        // We don't want to rely on an implicit order of struct fields.
        // So we drop the struct, field by field manually.
        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);""",
        """        // MUTATION M1: owner dropped before dependent.
        drop_in_place(&mut (*joined_ptr.as_ptr()).owner);
        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);
        dealloc(joined_ptr.as_ptr() as *mut u8, Layout::new::<JoinedCell<Owner, Dependent>>());""",
    )],
    "m2_uaf": [(
        "src/unsafe_self_cell.rs",
        """        // Drop dependent
        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);

        mem::forget(drop_guard);

        let owner_ptr: *const Owner = &(*joined_ptr.as_ptr()).owner;""",
        """        // MUTATION M2: free the allocation before running the dependent's dtor.
        mem::forget(drop_guard);
        let owner = read(&(*joined_ptr.as_ptr()).owner as *const Owner);
        dealloc(self.joined_void_ptr.as_ptr(), Layout::new::<JoinedCell<Owner, Dependent>>());
        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);
        return owner;
        #[allow(unreachable_code)]
        let owner_ptr: *const Owner = &(*joined_ptr.as_ptr()).owner;""",
    )],
    "m3_double_free": [(
        "src/lib.rs",
        """                // Allowing drop_guard to finish would let it double free owner.
                // So we dealloc the JoinedCell here manually.
                ::core::mem::forget(drop_guard);""",
        """                // MUTATION M3: the drop guard is left armed.""",
    )],
    "m4_leak": [(
        "src/unsafe_self_cell.rs",
        """        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);

        // Dropping owner
        // and deallocating
        // due to _guard at end of scope.""",
        """        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);

        // MUTATION M4: disarm the guard, leaking the owner and the allocation.
        mem::forget(_guard);""",
    )],
    "m5_alloc_leak": [(
        "src/unsafe_self_cell.rs",
        """        impl Drop for DeallocGuard {
            fn drop(&mut self) {
                unsafe { dealloc(self.ptr, self.layout) }
            }
        }""",
        """        impl Drop for DeallocGuard {
            fn drop(&mut self) {
                // MUTATION M5: destructors still run, the memory is never freed.
                let _ = (self.ptr, self.layout);
            }
        }""",
    )],
    "m6_read_before_drop": [(
        "src/unsafe_self_cell.rs",
        """        // Drop dependent
        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);

        mem::forget(drop_guard);

        let owner_ptr: *const Owner = &(*joined_ptr.as_ptr()).owner;

        // Move owner out so it can be returned.
        // Must not read before dropping dependent!! (Which happened above.)
        let owner = read(owner_ptr);""",
        """        // MUTATION M6: read the owner out before the dependent's destructor runs.
        mem::forget(drop_guard);

        let owner_ptr: *const Owner = &(*joined_ptr.as_ptr()).owner;
        let owner = read(owner_ptr);

        drop_in_place(&mut (*joined_ptr.as_ptr()).dependent);""",
    )],
    "m7_ok_path_guard": [(
        "src/lib.rs",
        """            ::core::result::Result::Ok(dependent) => {
                dependent_ptr_send.write(dependent);

                ::core::mem::forget(drop_guard);

                ::core::result::Result::Ok(Self {
                    unsafe_self_cell: $crate::unsafe_self_cell::UnsafeSelfCell::new(
                        joined_void_ptr_send.into_non_null().unwrap(),
                    ),
                    $(owner_marker: $crate::_covariant_owner_marker_ctor!($OwnerLifetime) ,)?
                })
            }
            ::core::result::Result::Err(err) => ::core::result::Result::Err(err)""",
        """            ::core::result::Result::Ok(dependent) => {
                dependent_ptr_send.write(dependent);

                // MUTATION M7: the guard is left armed on the success path.

                ::core::result::Result::Ok(Self {
                    unsafe_self_cell: $crate::unsafe_self_cell::UnsafeSelfCell::new(
                        joined_void_ptr_send.into_non_null().unwrap(),
                    ),
                    $(owner_marker: $crate::_covariant_owner_marker_ctor!($OwnerLifetime) ,)?
                })
            }
            ::core::result::Result::Err(err) => ::core::result::Result::Err(err)""",
    )],
    "m8_wrong_dealloc_layout": [(
        "src/unsafe_self_cell.rs",
        """        // Deallocate JoinedCell
        let layout = Layout::new::<JoinedCell<Owner, Dependent>>();
        dealloc(self.joined_void_ptr.as_ptr(), layout);""",
        """        // MUTATION M8: free with the owner's layout, not the whole cell's.
        let layout = Layout::new::<Owner>();
        dealloc(self.joined_void_ptr.as_ptr(), layout);""",
    )],

    # --- Contract-level bugs. ------------------------------------------------
    # These exist to show the contracts are load-bearing. m9 in particular is
    # invisible to every behavioural harness: writing a byte the cell does not
    # use changes no observable value. Only the `modifies()` frame condition
    # rules it out.
    "m9_accessor_writes": [(
        "src/unsafe_self_cell.rs",
        """    pub unsafe fn borrow_owner<'a, Dependent>(&'a self) -> &'a Owner {
        let joined_ptr = self.joined_void_ptr.cast::<JoinedCell<Owner, Dependent>>();

        &(*joined_ptr.as_ptr()).owner
    }""",
        """    pub unsafe fn borrow_owner<'a, Dependent>(&'a self) -> &'a Owner {
        let joined_ptr = self.joined_void_ptr.cast::<JoinedCell<Owner, Dependent>>();

        // MUTATION M9: a read-only accessor that writes. Violates modifies().
        let scribble = self.joined_void_ptr.as_ptr();
        scribble.write_volatile(scribble.read_volatile());

        &(*joined_ptr.as_ptr()).owner
    }""",
    )],
    "m10_overlapping_fields": [(
        "src/unsafe_self_cell.rs",
        """        let owner_ptr = core::ptr::addr_of_mut!((*this).owner);
        let dependent_ptr = core::ptr::addr_of_mut!((*this).dependent);

        (owner_ptr, dependent_ptr)
    }

    #[doc(hidden)]
    #[cfg(feature = "old_rust")]
    #[rustversion::since(1.51)]""",
        """        let owner_ptr = core::ptr::addr_of_mut!((*this).owner);

        // MUTATION M10: both fields carved out of the same bytes.
        let dependent_ptr = owner_ptr as *mut Dependent;

        (owner_ptr, dependent_ptr)
    }

    #[doc(hidden)]
    #[cfg(feature = "old_rust")]
    #[rustversion::since(1.51)]""",
    )],
    "m11_lock_not_taken": [(
        "src/unsafe_self_cell.rs",
        """        let was_locked = self.is_locked.swap(true, Ordering::Relaxed);""",
        """        // MUTATION M11: read the flag without setting it, so the lock never
        // latches and a second borrow_mut would alias.
        let was_locked = self.is_locked.load(Ordering::Relaxed);""",
    )],
}


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        base = tmp / "base"
        base.mkdir()
        for rel in SOURCES:
            (base / rel).parent.mkdir(parents=True, exist_ok=True)
            (base / rel).write_text((CRATE / rel).read_text())

        for name, edits in MUTATIONS.items():
            target = tmp / name
            target.mkdir()
            for rel in SOURCES:
                (target / rel).parent.mkdir(parents=True, exist_ok=True)
                (target / rel).write_text((base / rel).read_text())

            for rel, find, replace in edits:
                text = (target / rel).read_text()
                if find not in text:
                    print(f"{name}: pattern not found in {rel}", file=sys.stderr)
                    return 1
                (target / rel).write_text(text.replace(find, replace, 1))

            chunks = []
            for rel in SOURCES:
                diff = subprocess.run(
                    ["diff", "-u", "--label", f"a/{rel}", "--label", f"b/{rel}",
                     str(base / rel), str(target / rel)],
                    capture_output=True, text=True,
                )
                chunks.append(diff.stdout)
            (HERE / f"{name}.patch").write_text("".join(chunks))
            print(f"wrote {name}.patch")

    return 0


if __name__ == "__main__":
    sys.exit(main())
