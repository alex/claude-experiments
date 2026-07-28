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

Verified with Kani 0.67.0 (which pins its own `nightly-2025-11-21` toolchain).

```sh
cargo install --locked kani-verifier
cargo kani setup

./verify.sh                                   # everything
./verify.sh --harness into_owner              # a subset
./verify.sh --randomize-layout=42             # see "Layout independence"

./mutants/run.sh                              # check the suite isn't vacuous
```

The behavioural harnesses live in a separate crate. The crate itself carries
Kani *function contracts* — see below — which are the only edits to upstream:
116 added lines, nothing modified or removed, every one of them behind
`#[cfg_attr(kani, ...)]` so ordinary builds and `cargo test` are unaffected.

A full run is about two minutes.

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
| `mut_borrow` | the first `borrow_mut` always succeeds and writes through; the lock is one-way, so subsequent attempts panic rather than alias — including via `borrow_owner` on an already-built cell, and however many times they are repeated; the `&mut` round trip through a cell preserves writes |
| `pointer_stability` | addresses survive moves through stack, `Box` and tuple; both fields land aligned and disjoint inside one allocation, for a high-alignment owner and for a high-alignment dependent; the generated struct is pointer-sized with its `NonNull` niche intact |
| `owner_immutability` | invariant 2 — "owner is NEVER changed again" — over a fully symbolic byte array, across every operation the public API allows; and the ordering claim behind *"Must not read before dropping dependent!!"*, observed through an owner with interior mutability that the dependent's destructor writes to |
| `drop_guard` | `OwnerAndCellDropGuard` destroys the owner exactly once and frees the whole `JoinedCell`, not just the owner's share of it; `mem::forget`ing it hands responsibility back intact |
| `shapes` | zero-sized owner, zero-sized dependent, an owner holding its own `Box`, an owner that is itself a borrow (the macro's optional owner lifetime), and a cell where neither side has a destructor |
| `op_sequence` | bounded-length *arbitrary* sequences of public calls, with the invariants re-checked after every step and a nondeterministic choice of `Drop` or `into_owner` at the end |
| `async_builder` | the `async_builder` constructors, including cancellation — dropping the future mid-`await`, which is the one path that reaches the drop guard through the public API without unwinding |
| `arbitrary_callbacks` | the same properties over *symbolic* builders and visitors rather than one hand-written closure each — see below |
| `contracts` | discharges the function contracts written on the crate itself, against arbitrary inputs satisfying each precondition — see below |

The instrumented owner in `tracking.rs` writes a poison canary in its
destructor, and the dependent's destructor reads the owner through the
self-reference. That is what makes wrong *ordering* observable and not merely
wrong drop counts: reading a freed allocation is a Kani pointer failure, and
reading a destroyed-but-not-freed owner trips the canary.

## Contracts on the crate itself

A harness proves things about the call sequences it happens to write. A contract
states the obligation on the *function*, and `#[kani::proof_for_contract]`
discharges it against an arbitrary input satisfying the precondition — so what
is proved stops depending on how the function was reached.

Two kinds of claim are new here, and neither can be expressed by a harness at
all:

**Frame conditions.** `#[kani::modifies()]` with no targets says a function
writes to *nothing*. On `borrow_owner`, `borrow_dependent` and `borrow_mut`
that is the machine-checked form of invariant 4 — "the only access to owner and
dependent is as immutable reference". No amount of checking return values can
establish "and it wrote nowhere else".

**Layout obligations, stated once at the source.** `JoinedCell::_field_pointers`
is what every other unsafe function is built on. Its contract says the two
pointers land in the allocation, are aligned for the type each will hold, and
never overlap — so writing the dependent cannot disturb the owner the dependent
borrows. Five `proof_for_contract` harnesses monomorphise it across the shapes
that could plausibly break the arithmetic, including a zero-sized field on
either side.

The rest: `UnsafeSelfCell::new` stores the pointer it was given,
`SendMutPtr::into_non_null` is `Some` exactly when the pointer is non-null, and
`MutBorrow::borrow_mut` — given an unlocked cell — leaves it locked and returns
a reference to the wrapped value itself. That last contract describes only the
non-panicking path; that the *locked* path panics rather than aliasing is proved
separately by the `should_panic` harnesses in `mut_borrow`.

`verify.sh` passes `-Z function-contracts`, which asserts contracts at call
sites as well. So the `modifies()` clauses are checked in all 71 harnesses, not
only in the eleven that target the contracts directly.

One precondition is weaker than it should be, for a Kani reason worth recording.
The natural predicate for the accessors is `can_dereference` — the bytes are
allocated, aligned, *and* form a valid `JoinedCell`. Kani cannot check validity
of a type containing an enum, and a user's `Dependent` is allowed to contain
one, so the preconditions use `can_write` (allocated, aligned, right size)
instead. Being weaker, it makes the contract harder to satisfy rather than
easier — the function must be correct for more states, not fewer.

## Quantifying over the callbacks

Every entry point takes a user callback. A harness that passes one concrete
closure proves the property for that closure, which is a weak reading of "the
crate is correct".

Kani cannot quantify over code — it model-checks one monomorphic program. But
the quantification can be pushed down to values, because `self_cell` never
inspects the callback: it calls it, and does the same thing with whatever comes
back. So "for all builders" reduces to "for all things a builder could return,
and all the ways it could get there", and that part *is* symbolic.
`arbitrary_callbacks` makes each of those choices a `kani::any()`:

* **The return value.** The dependent's scalar fields are nondeterministic.
* **The self-reference.** A builder cannot conjure a `&'a Owner`; the only one
  in scope is its argument. So the reachable choices are exactly three — ignore
  the owner, keep the whole owner, keep a reference into it — and the `Anchor`
  enum enumerates them with a symbolic choice.
* **Control flow.** Whether a fallible builder returns `Ok` or `Err`, and which
  error, is symbolic.
* **Side effects.** The only state a builder can touch is the owner it was
  handed, and only through interior mutability. How many times it writes is
  symbolic.
* **Visitors.** Whether `with_dependent_mut` leaves the dependent alone, edits
  it, or replaces it wholesale — which runs the old dependent's destructor
  inside a live cell — is symbolic, as is what it replaces it with.

`every_builder_outcome_is_reachable` backs that up with `kani::cover!`: all nine
outcomes come back SATISFIED, so no stray `assume` has quietly pruned a branch
and left the other harnesses passing for the wrong reason.

Two things stay outside even this. A callback that *panics* — no unwinding under
Kani, so that path is covered instead by `drop_guard` and
`async_builder::cancelling_construction_cleans_up`. And other dependent *types*:
the quantification is over the values of a fixed type, not over the type.

## Verification is not vacuous

A proof suite that passes is only worth something if it would have failed on a
broken implementation. `mutants/` holds patches that each introduce one classic
bug into `self_cell`. `mutants/generate.py` turns them into patches against the
current source, and `mutants/run.sh` applies each to a throwaway copy and
re-runs the suite. All eleven are detected:

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
| `m9_accessor_writes` | `borrow_owner` writes a byte back to the cell | the `modifies()` frame condition — **nothing else in the suite sees this** |
| `m10_overlapping_fields` | `_field_pointers` carves both fields out of the same bytes | the disjointness clause of the `_field_pointers` contract |
| `m11_lock_not_taken` | `MutBorrow::borrow_mut` reads the flag instead of swapping it, so the lock never latches | the `borrow_mut` contract's postcondition |

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

* **`#[kani::should_panic]` is weaker than it looks.** It succeeds if *at least
  one* execution panics, not if all of them do: a harness that panics only when
  `kani::any::<u8>() == 7` passes just as happily. Every `should_panic` harness
  here is therefore written with no nondeterminism on the path to the panic, so
  that "some execution panics" and "this always panics" coincide. Read them as
  case analysis over fixed sequences, not as universally quantified claims.
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
