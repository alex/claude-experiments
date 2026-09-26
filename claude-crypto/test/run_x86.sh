#!/bin/sh
# Runs the x86-64 tests natively (needs an x86-64 CPU with AVX2, BMI1/2, MOVBE):
#  1. instruction-level differential test of the Lean model (x86_insn_test.c
#     produces vectors on the CPU, X86InsnCheck.lean checks them against
#     CC.X86.exec / CC.X86.evalCond).  The form table of x86_insn_test.c is
#     generated from X86InsnCheck.lean; `run_x86.sh --regen` regenerates it,
#     and the test refuses to run with a stale table;
#  2. the generated SHA-256 block functions (scalar and AVX2) against a
#     portable reference;
#  3. the generated P-384 ECDSA verifier against the OpenSSL-generated test
#     vectors of p384_vectors.txt (see p384_gen.c).
# Requires gcc and the Lean toolchain.  The SHA-extension forms are tested if
# CPUID reports SHA, or if X86_INSN_FORCE_SHA=1 is set (for CPUs that execute
# the instructions without advertising them).  Step 2 also tests the SHA-NI
# block function under the same condition.  The instruction test takes ~3 minutes
# (about 370k vectors); `run_x86.sh [--regen] N` uses N random vectors per form
# instead of 512 (the checker requires at least 500 vectors per form).
set -e
cd "$(dirname "$0")"
command -v lake > /dev/null || PATH="$HOME/.elan/bin:$PATH"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
(cd ../lean && lake env lean --run ../test/X86InsnCheck.lean --gen) > "$out/gen.h"
if [ "$1" = "--regen" ]; then
  shift
  awk -v gen="$out/gen.h" '
    /END GENERATED FORMS/ { while ((getline l < gen) > 0) print l; skip = 0 }
    !skip { print }
    /BEGIN GENERATED FORMS/ { skip = 1 }' x86_insn_test.c > "$out/new.c"
  cp "$out/new.c" x86_insn_test.c
fi
awk '/BEGIN GENERATED FORMS/ { f = 1; next } /END GENERATED FORMS/ { f = 0 } f' x86_insn_test.c > "$out/cur.h"
if ! cmp -s "$out/gen.h" "$out/cur.h"; then
  echo "the form table of x86_insn_test.c is out of date: run $0 --regen" >&2
  exit 1
fi
gcc -O1 -static x86_insn_test.c -o "$out/x86_insn_test"
"$out/x86_insn_test" ${1:-512} > "$out/vectors.txt"
(cd ../lean && lake env lean --run ../test/X86InsnCheck.lean "$out/vectors.txt")
impls="scalar avx2"
if [ "${X86_INSN_FORCE_SHA:-0}" != 0 ] || grep -qw sha_ni /proc/cpuinfo 2>/dev/null; then
  impls="$impls shani"
fi
for impl in $impls; do
  echo "sha256_$impl:"
  gcc -O2 -static -DNO_OPENSSL -DSHA_BLOCKS=cc_sha256_blocks_x86_$impl \
    sha256_test.c ../asm/x86_64/sha256_$impl.S -o "$out/sha256_test"
  "$out/sha256_test"
done
gcc -O2 -static -DNO_OPENSSL p384_test.c ../asm/x86_64/p384_verify.S -o "$out/p384_test"
"$out/p384_test" p384_vectors.txt 20
