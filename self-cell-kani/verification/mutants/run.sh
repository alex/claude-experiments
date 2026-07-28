#!/usr/bin/env bash
#
# Mutation-test the proof suite.
#
# A proof suite that passes is only interesting if it would have failed on a
# broken implementation. This script applies each patch in this directory to a
# throwaway copy of self_cell, re-runs the harnesses against it, and reports
# whether the suite noticed.
#
# Every mutant must FAIL. A mutant that verifies clean means the corresponding
# property is not actually being checked.

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
crate_root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

status=0

for patch in "$here"/*.patch; do
  name="$(basename "$patch" .patch)"

  rm -rf "$work/$name"
  mkdir -p "$work/$name"
  # Copy the crate but not build artefacts.
  tar -C "$crate_root" --exclude=target --exclude=mutants -cf - . | tar -C "$work/$name" -xf -

  if ! patch -s -p1 -d "$work/$name" < "$patch"; then
    echo "MUTANT $name: FAILED TO APPLY"
    status=1
    continue
  fi

  output="$("$work/$name/verification/verify.sh" 2>&1)"
  if grep -q '0 failures' <<<"$output"; then
    echo "MUTANT $name: SURVIVED  <-- the suite does not detect this bug"
    status=1
  else
    echo -n "MUTANT $name: killed by "
    grep -oE 'Verification failed for - [^ ]+' <<<"$output" | sed 's/Verification failed for - //' | paste -sd, -
  fi
done

exit "$status"
