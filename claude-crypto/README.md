# claude-crypto

Formally verified assembly implementations of cryptographic algorithms for
x86-64, AArch64 and ppc64le, with the proofs in Lean 4, and a Rust crate that
exposes them.

| Algorithm | Arch | Implementation | Functional correctness | Constant time |
|---|---|---|---|---|
| SHA-256 (compression function over n blocks) | x86-64 | scalar (BMI2) | ✅ `CC.X86.SHA256Scalar.correct` | ✅ `…Scalar.constant_time` |
| | x86-64 | AVX2 (2 blocks/iteration, vectorised schedule) | ✅ `CC.X86.SHA256Avx2.correct` | ✅ `…Avx2.constant_time` |
| | AArch64 | ARMv8 crypto extensions | ✅ `CC.Arm.SHA256Ce.correct` | ✅ `…Ce.constant_time` |
| | ppc64le | POWER8 vector crypto | ✅ `CC.Ppc.SHA256P8.correct` | ✅ `…P8.constant_time` |
| ECDSA P-384 signature verification | IR (below) | Montgomery field arithmetic, Fermat inversion, Shamir double-scalar ladder | ✅ `CC.P384.main_ok` | n/a (public inputs) |
| | x86-64 (BMI2) | compiled from the IR by a verified compiler | ✅ `CC.P384.x86_correct` | n/a |
| | AArch64 | compiled from the IR by a verified compiler | ✅ `CC.P384.arm_correct` | n/a |
| | ppc64le | compiled from the IR by a verified compiler | ✅ `CC.P384.ppc_correct` | n/a |

## What is proven, and what you have to trust

Every theorem is about the **machine code**: a Lean model of each ISA
(`X86/Basic.lean`, `Arm/Basic.lean`, `Ppc/Basic.lean`) executes the program,
and `WP` (`Framework/Code.lean`) is total correctness: the code terminates
without faulting (every memory access stays within the regions it was given)
in a state satisfying the postcondition.  The `.S` files in `asm/` are
printed from the same Lean terms (`lake exe emit`).

To trust a result you need to review:

1. **The specifications** (short, and written to be read next to the standards):
   * `lean/ClaudeCrypto/Spec/SHA256.lean` – FIPS 180-4.
   * `lean/ClaudeCrypto/Spec/P384.lean` – FIPS 186-5 §6.4.2 ECDSA verification
     and SP 800-186 P-384.  The group law is Mathlib's
     (`WeierstrassCurve.Affine.Point`), so no point formulas need review;
     the curve constants are in `Spec/P384Facts.lean` (primality of `p` and `n`
     is proven with Pratt certificates checked by the kernel).
2. **The statement of each top-level theorem** (preconditions on registers and
   memory regions, postcondition).
3. **The trusted computing base**:
   * the ISA models (`*/Basic.lean`), which transcribe the vendor pseudocode.
     The AArch64 and ppc64le models are differentially tested against QEMU
     (`test/run_aarch64.sh`, `test/run_ppc64le.sh`: tens of thousands of
     random instruction vectors); the x86-64 model against hardware is in
     progress;
   * the printers (`*/Print.lean`) and the assembler/linker;
   * Lean's kernel, and the axioms `propext`, `Classical.choice`, `Quot.sound`
     (no `sorry`, `native_decide` or `bv_decide` anywhere in the proofs).

Everything else — the IR, the compilers, the P-384 field/point/scalar
programs, all intermediate lemmas — is checked by Lean and need not be read.

### Constant time

`constant_time` theorems say: two runs from states that agree on the public
inputs (pointers, lengths) produce identical traces of branch decisions and
memory addresses.  They are proven by a taint analysis (`Framework/Taint.lean`,
with a soundness proof) evaluated by the kernel.

The P-384 code verifies signatures, whose inputs are all public, so it is
**not** constant time and must not be reused for secret data (e.g. the
modular reduction branches on its result).

## Layout

```
lean/ClaudeCrypto/
  Framework/   Code (block/seq/ite/loop), semantics, WP, taint analysis, verified compilation
  Common/      byte-addressed memory, regions, separation
  Spec/        SHA-256 and P-384 specifications (+ primality certificates, Jacobian formulas)
  X86/ Arm/ Ppc/   ISA models, printers, symbolic-execution tactics, SHA-256 proofs
  Limb/        a small multi-precision IR, verified compilers IR→x86-64/AArch64/ppc64le,
               Montgomery multiplication, modular add/sub, field programs
  P384/        the P-384 verifier as an IR program and its proof
asm/           generated assembly
rust/          the `claude_crypto` crate (runtime CPU dispatch)
test/          C harnesses, test vectors, instruction-level differential tests
```

### P-384 structure

The verifier is written once in the limb IR (`P384/Prog.lean`) and compiled
to each architecture by a compiler with a per-instruction simulation proof
(`Limb/X86.lean`, `Limb/Arm.lean`, `Limb/Ppc.lean`; `Framework/Compile.lean`
lifts it to whole programs).  The IR proof is layered:

* `Limb/Mont*.lean`, `Limb/AddSub.lean`: 6-limb Montgomery multiplication
  (CIOS), modular addition/subtraction;
* `Limb/FProg.lean`: straight-line *field programs* over 48-byte frame slots,
  with meaning in `ZMod N`;
* `P384/Point.lean`, `P384/PointOps.lean`: Jacobian doubling (dbl-2001-b) and
  addition (add-2007-bl) with every special case (`P = 0`, `Q = 0`, `P = Q`,
  `P = −Q`), proven against Mathlib's group law via `Spec/P384Jacobian.lean`;
* `P384/Scalar.lean`: `s⁻¹ = s^(n−2) mod n`, `u₁ = e·s⁻¹`, `u₂ = r·s⁻¹`;
* `P384/Ladder.lean`: `u₁·G + u₂·Q` (joint bits, table `{G, Q, G+Q}`);
* `P384/Final.lean`: `x_R mod n = r` without inverting `Z`;
* `P384/Main.lean`: input validation and the end-to-end `main_ok`.

## Performance

Measured on the development machine (Xeon, no SHA-NI), OpenSSL 3.0.13:

| | this crate | OpenSSL |
|---|---|---|
| SHA-256, 16 KiB messages (AVX2) | ~400 MB/s | ~395 MB/s |
| SHA-256, 64-byte messages | ~175 MB/s | ~82 MB/s |
| ECDSA P-384 verify | ~1790 verify/s | ~1280 verify/s |

(AArch64 and ppc64le code was tested under QEMU only.)

## Building and checking

```sh
cd lean && lake build           # checks every proof
lake exe emit ../asm            # regenerates asm/
cd ../rust && cargo test        # runs the Rust tests (x86-64 natively; see .cargo/config.toml for qemu targets)
sh test/run_aarch64.sh          # instruction-level + end-to-end tests under qemu
sh test/run_ppc64le.sh
```

The machine needs roughly 8 GB of memory for the largest proof files.
