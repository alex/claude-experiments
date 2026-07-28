#!/usr/bin/env bash
#
# Run the Kani proof suite for self_cell.
#
# Usage:
#   ./verify.sh                       # all harnesses
#   ./verify.sh --harness <filter>    # a subset; any extra args go to cargo kani
#
# Requires: cargo install --locked kani-verifier && cargo kani setup

set -euo pipefail

cd "$(dirname "$0")"

# --memory-leak-check is a CBMC option rather than a Kani one, so it has to go
# through --cbmc-args, which in turn requires -Z unstable-options. Without it
# an allocation that is simply never freed verifies clean -- see README.md.
# -Z function-contracts turns on the contracts written on the crate itself. It
# is not only for the `contracts` module: with it on, Kani asserts those
# contracts at every call site, so the `modifies()` frame conditions are
# checked in all the other harnesses too.
# -Z mem-predicates supplies can_write / can_dereference / same_allocation,
# which the preconditions use.
exec cargo kani \
  -j --output-format=terse \
  -Z unstable-options \
  -Z function-contracts \
  -Z mem-predicates \
  --extra-pointer-checks \
  "$@" \
  --cbmc-args --memory-leak-check
