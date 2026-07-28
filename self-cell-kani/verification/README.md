# Formal verification of `self_cell` with Kani

[Kani](https://model-checking.github.io/kani/) is a bit-precise bounded model
checker for Rust. It compiles a program to a logical formula and asks a SAT/SMT
solver whether any execution can violate a property — so a passing harness is a
proof over *all* values of its nondeterministic inputs, not a sample of them.

`self_cell` is a good target. It is small (~200 lines of `unsafe`), and that
`unsafe` does exactly the kind of thing a model checker is built for: a raw
`alloc`, two field pointers carved out of it with `addr_of_mut!`, a
self-reference written into the second field pointing at the first, hand-rolled
field-by-field destruction, and drop guards that have to release the right
things exactly once on every path.

## Running

```sh
cargo install --locked kani-verifier
cargo kani setup

./verify.sh                                   # everything
./verify.sh --harness into_owner              # a subset
./verify.sh --randomize-layout=42             # see "Layout independence"

./mutants/run.sh                              # check the suite isn't vacuous
```

The harnesses live in a separate crate so that `../src` stays byte-for-byte
identical to upstream. A full run is about four minutes; the `async_builder`
harnesses dominate it.

## What is checked

Kani's default checks (pointer validity, use-after-free, double free,
out-of-bounds, arithmetic overflow, panics, unreachable code) apply throughout.
On top of those, the harnesses assert the crate's own invariants.

| Module | Obligation |
| --- | --- |
| `construct_drop` | `new` allocates and builds in place without memory error; `Drop` destroys the dependent strictly before the owner it borrows; each is destroyed exactly once; the self-reference is live throughout the dependent's destructor; independent cells do not disturb each other |
| `data_integrity` | every accessor round-trips the stored bytes; `with_dependent_mut` writes land in the heap allocation; the owner and dependent occupy disjoint memory; `not_covariant` cells behave identically on the `with_dependent` path |
| `into_owner` | the dependent is destroyed before the owner is `ptr::read` out; the owner is returned without being dropped; the allocation is freed exactly once and no other cell's is touched |
| `fallible` | `try_new` drops the owner exactly once on failure; `try_new_or_recover` hands the owner back live and un-dropped; both free the allocation exactly once; a recovered owner can be reused to build a working cell |
| `mut_borrow` | `MutBorrow`'s lock is one-way: the first `borrow_mut` always succeeds and *no* sequence of two or more gets past it, including via `borrow_owner` on an already-built cell; the `&mut` round trip through a cell preserves writes |
| `pointer_stability` | addresses survive moves through stack, `Box` and tuple; both fields land aligned and disjoint inside one allocation, for a high-alignment owner and for a high-alignment dependent; the generated struct is pointer-sized with its `NonNull` niche intact |
| `owner_immutability` | invariant 2 — "owner is NEVER changed again" — over a fully symbolic byte array, across every operation the public API allows; and the ordering claim behind *"Must not read before dropping dependent!!"*, observed through an owner with interior mutability that the dependent's destructor writes to |
| `drop_guard` | `OwnerAndCellDropGuard` destroys the owner exactly once and frees the whole `JoinedCell`, not just the owner's share of it; `mem::forget`ing it hands responsibility back intact |
| `shapes` | zero-sized owner, zero-sized dependent, an owner holding its own `Box`, an owner that is itself a borrow (the macro's optional owner lifetime), and a cell where neither side has a destructor |
| `op_sequence` | bounded-length *arbitrary* sequences of public calls, with the invariants re-checked after every step and a nondeterministic choice of `Drop` or `into_owner` at the end |
| `async_builder` | the `async_builder` constructors, including cancellation — dropping the future mid-`await`, which is the one path that reaches the drop guard through the public API without unwinding |

The instrumented owner in `tracking.rs` writes a poison canary in its
destructor, and the dependent's destructor reads the owner through the
self-reference. That is what makes wrong *ordering* observable and not merely
wrong drop counts: reading a freed allocation is a Kani pointer failure, and
reading a destroyed-but-not-freed owner trips the canary.

## Verification is not vacuous

A proof suite that passes is only worth something if it would have failed on a
broken implementation. `mutants/` holds patches that each introduce one classic
bug into `self_cell`; `mutants/run.sh` applies each to a throwaway copy and
re-runs the suite. All eight are detected:

| Mutant | Injected bug | Detected as |
| --- | --- | --- |
| `m1_drop_order` | `drop_joined` destroys the owner before the dependent | canary: *"dependent outlived its owner's destructor"* |
| `m2_uaf` | `into_owner` frees the allocation before running the dependent's destructor | *dereference failure: deallocated dynamic object* |
| `m3_double_free` | `try_new_or_recover`'s error path leaves the drop guard armed | *double free*, plus the recovered owner having been dropped |
| `m4_leak` | `drop_joined` disarms its guard, leaking the owner and the allocation | drop-count assertions |
| `m5_alloc_leak` | destructors still run but the memory is never freed | *dynamically allocated memory never freed* |
| `m6_read_before_drop` | `into_owner` `ptr::read`s the owner out before running the dependent's destructor | the destructor's write-back missing from the recovered owner |
| `m7_ok_path_guard` | `try_new`'s *success* path leaves the drop guard armed | owner destroyed while the cell is still live |
| `m8_wrong_dealloc_layout` | `into_owner` frees with `Layout::new::<Owner>()` instead of the whole cell's | *rust_dealloc must be called on an object whose allocated size matches its layout* |

`m5` is the reason `verify.sh` passes `--cbmc-args --memory-leak-check`: without
it, an allocation that is simply never released verifies clean. `m6` is caught
by exactly one harness, `owner_immutability::into_owner_sees_the_dependents_writeback`
— nothing else in the suite can see the difference.

## Layout independence

`JoinedCell<Owner, Dependent>` is `repr(Rust)`, so the compiler is free to order
its two fields however it likes, and the crate is only correct if it never
assumes an order — which is why it carves out field pointers with `addr_of_mut!`
rather than by offset. `--randomize-layout=<seed>` makes rustc actually shuffle
struct layouts, so it turns that "never assumes" into something checkable:

```sh
./verify.sh --randomize-layout=1
./verify.sh --randomize-layout=7
./verify.sh --randomize-layout=42
```

All three pass, all 53 harnesses each.

## Limits of this verification

Worth stating plainly, since "formally verified" invites over-reading.

* **Kani does not model aliasing.** Stacked Borrows / Tree Borrows violations —
  the class of bug Miri finds — are outside its model. Upstream runs Miri in CI,
  so the two are complementary rather than redundant.
* **No unwinding.** Kani compiles with `panic=abort`, so a panic is a verification
  failure rather than something that unwinds. A *panicking* dependent builder
  therefore cannot be used to reach `OwnerAndCellDropGuard`. Two harnesses cover
  it another way: `async_builder::cancelling_construction_cleans_up` drops the
  constructor's future mid-`await`, which reaches the armed guard through the
  public API with no unwinding involved, and `drop_guard` reproduces the state a
  panicking builder leaves behind and runs the guard against it directly.
* **No concurrency.** Kani treats atomics as sequential operations. The `Send`
  and `Sync` reasoning for `UnsafeSelfCell`, `SendMutPtr` and `MutBorrow` is
  type-level and outside what Kani checks.
* **Monomorphic.** Each harness fixes concrete owner and dependent types. The
  suite covers a deliberate spread — high-alignment owner, high-alignment
  dependent, `&mut` dependent via `MutBorrow`, covariant and `not_covariant`,
  types with and without destructors — but this is case analysis, not a proof
  for all `Owner` and `Dependent`.
* **`-Z valid-value-checks` is unusable here.** It reports the `addr_of_mut!`
  calls in `JoinedCell::_field_pointers` as invalid values. That is a Kani
  limitation, not a `self_cell` defect: `addr_of_mut!` on uninitialized memory is
  precisely the sanctioned idiom, and a standalone snippet using it with no
  `self_cell` involved is flagged the same way. `-Z uninit-checks` currently
  crashes the Kani compiler on this crate.
* **Async builders are written around two Kani bugs.** Kani 0.67 cannot lower
  `async` closures at all (`not yet implemented: FIXME(async_closures): Lower
  these to SMIR`), so the builders in `async_builder` are free `async fn` items
  with their would-be captures passed through statics. `kani::block_on` also
  does not converge here, so the futures are polled by hand.
