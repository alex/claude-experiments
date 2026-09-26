#!/bin/sh
# Cross-compiles and runs the ppc64le tests under QEMU user-mode emulation
# (POWER8 CPU model):
#  1. instruction-level differential test of the Lean model (ppc_insn_test.c
#     produces vectors on "hardware", PpcInsnCheck.lean checks them against
#     CC.Ppc.exec);
#  2. the generated SHA-256 block function against a portable reference;
#  3. the generated P-384 ECDSA verifier against the (OpenSSL-generated) test
#     vectors of p384_vectors.txt (see p384_gen.c), on POWER8 and POWER9.
# Requires powerpc64le-linux-gnu-gcc, qemu-ppc64le and the Lean toolchain.
set -e
cd "$(dirname "$0")"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
QEMU="qemu-ppc64le -cpu power8"
powerpc64le-linux-gnu-gcc -O1 -static -mcpu=power8 ppc_insn_test.c -o "$out/ppc_insn_test"
$QEMU "$out/ppc_insn_test" > "$out/vectors.txt"
(cd ../lean && lake env lean --run ../test/PpcInsnCheck.lean "$out/vectors.txt")
powerpc64le-linux-gnu-gcc -O2 -static -mcpu=power8 -DNO_OPENSSL -DSHA_BLOCKS=cc_sha256_blocks_ppc64le \
  sha256_test.c ../asm/ppc64le/sha256.S -o "$out/sha256_test"
$QEMU "$out/sha256_test"
powerpc64le-linux-gnu-gcc -O2 -static -mcpu=power8 -DNO_OPENSSL -DP384_VERIFY=cc_p384_verify_ppc64le \
  p384_test.c ../asm/ppc64le/p384_verify.S -o "$out/p384_test"
$QEMU "$out/p384_test" p384_vectors.txt 20
qemu-ppc64le -cpu power9 "$out/p384_test" p384_vectors.txt 20
