#!/bin/sh
# Cross-compiles and runs the AArch64 tests under QEMU user-mode emulation:
#  1. instruction-level differential test of the Lean model (arm_insn_test.c
#     produces vectors on "hardware", ArmInsnCheck.lean checks them against
#     CC.Arm.exec);
#  2. the generated SHA-256 block function against a portable reference.
# Requires aarch64-linux-gnu-gcc, qemu-aarch64 and the Lean toolchain.
set -e
cd "$(dirname "$0")"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
QEMU="qemu-aarch64 -L /usr/aarch64-linux-gnu"
aarch64-linux-gnu-gcc -O1 -static -march=armv8-a+crypto arm_insn_test.c -o "$out/arm_insn_test"
$QEMU "$out/arm_insn_test" > "$out/vectors.txt"
(cd ../lean && lake env lean --run ../test/ArmInsnCheck.lean "$out/vectors.txt")
aarch64-linux-gnu-gcc -O2 -static -DNO_OPENSSL -DSHA_BLOCKS=cc_sha256_blocks_arm \
  sha256_test.c ../asm/aarch64/sha256.S -o "$out/sha256_test"
$QEMU "$out/sha256_test"
