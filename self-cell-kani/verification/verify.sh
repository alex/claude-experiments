#!/usr/bin/env bash
#
# Run the Kani proof suite for self_cell.
#
# Usage:
#   ./verify.sh                       # all harnesses (both passes)
#   ./verify.sh --harness <filter>    # a subset; extra args go to cargo kani
#                                     # and the second pass is skipped
#
# Requires: cargo install --locked kani-verifier && cargo kani setup

set -euo pipefail

cd "$(dirname "$0")"

# --memory-leak-check is a CBMC option rather than a Kani one, so it has to go
# through --cbmc-args, which in turn requires -Z unstable-options. Without it
# an allocation that is simply never freed verifies clean -- see README.md.
#
# -Z function-contracts turns on the contracts written on the crate itself. It
# is not only for the `contracts` module: with it on, Kani asserts those
# contracts at every call site, so the `modifies()` frame conditions are
# checked in all the other harnesses too.
#
# -Z mem-predicates supplies can_write / can_dereference / same_allocation,
# which the preconditions use.
COMMON=(
  -j --output-format=terse
  -Z unstable-options
  -Z function-contracts
  -Z mem-predicates
  --extra-pointer-checks
)

# Kani implements an asserted contract as an ordinary assertion, i.e. a panic.
# `#[kani::should_panic]` accepts *any* panic. So in a should_panic harness a
# violated contract is indistinguishable from the panic the harness exists to
# prove, and the harness passes either way -- which would make it blind to
# exactly the bugs it was written to catch. These are therefore re-run with
# contract assertions off, so that their only available panic is the real one.
SHOULD_PANIC_HARNESSES=(
  mut_borrow::second_borrow_mut_panics
  mut_borrow::lock_is_not_released_by_dropping_the_reference
  mut_borrow::borrow_owner_cannot_re_lock_a_built_cell
  mut_borrow::lock_stays_taken_across_repeated_attempts
  shapes::both_zero_sized_is_rejected
)

echo "== pass 1: all harnesses, contracts asserted at call sites"
cargo kani "${COMMON[@]}" "$@" --cbmc-args --memory-leak-check

# A filtered invocation is asking about a specific harness, so leave it alone.
if [ "$#" -gt 0 ]; then
  exit 0
fi

echo
echo "== pass 2: should_panic harnesses, contract assertions off"
filters=()
for harness in "${SHOULD_PANIC_HARNESSES[@]}"; do
  filters+=(--harness "$harness")
done
cargo kani "${COMMON[@]}" --no-assert-contracts --exact "${filters[@]}" \
  --cbmc-args --memory-leak-check
