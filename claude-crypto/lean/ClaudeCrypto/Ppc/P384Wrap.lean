import ClaudeCrypto.P384.Prog
import ClaudeCrypto.Limb.Ppc
import ClaudeCrypto.Ppc.Print

/-!
# `cc_p384_verify_ppc64le`: the ELFv2 wrapper around the P-384 verifier

`int cc_p384_verify_ppc64le(const uint8_t pubkey[96], const uint8_t digest[48], const uint8_t sig[96])`

The arguments arrive in `r3`, `r4`, `r5` and are moved to IR registers 5, 4 and
0 (`r8`, `r7`, `r3`: see `CC.Limb.Ppc.phys`); the result, IR register 1 (`r4`),
is returned in `r3`.  The compiled IR code writes `r0` and `r3`–`r12`
(volatile) and `r14`–`r18` (nonvolatile), and never touches `r1`, `r2`, `r13`,
`r19`–`r31`, the vector registers, CR1–CR7, or (net) the link register.

Stack frame (`frameBytes` = 1872 bytes, 16-byte aligned, allocated with
`stdu r1,-1872(r1)`, which also stores the back chain):

| offset from the new `r1` | contents                          |
|--------------------------|-----------------------------------|
| 0 … 31                   | ELFv2 frame header (back chain …) |
| 32 … 1823                | the IR frame (IR register 14)     |
| 1824 … 1863              | saved `r14`–`r18`                 |
| 1864 … 1871              | padding                           |

The code of `CC.P384.main` sets IR register 13 (`r17`) to the constants table
(with the `adr` pseudo-instruction, which uses `r0` and restores `LR`); the
table is emitted in `.text` right after the function.
-/

namespace CC.Ppc.P384Wrap

def name : String := "cc_p384_verify_ppc64le"

/-- Bytes of stack allocated. -/
def frameBytes : Nat := 1872

/-- Offset of the IR frame in the stack frame (after the ELFv2 frame header). -/
def irOff : Nat := 32

/-- Offset of the register save area. -/
def saveOff : Nat := 1824

theorem frameSize_le : irOff + CC.P384.frameSize ≤ saveOff := by decide
theorem frameBytes_aligned : frameBytes % 16 = 0 := by decide

def prologue : List Instr :=
  [ .stdu .r1 .r1 (-1872),
    .std .r14 .r1 1824, .std .r15 .r1 1832, .std .r16 .r1 1840, .std .r17 .r1 1848, .std .r18 .r1 1856,
    .addi .r18 .r1 32,
    .or .r8 .r3 .r3, .or .r7 .r4 .r4, .or .r3 .r5 .r5 ]

def epilogue : List Instr :=
  [ .or .r3 .r4 .r4,
    .ld .r14 .r1 1824, .ld .r15 .r1 1832, .ld .r16 .r1 1840, .ld .r17 .r1 1848, .ld .r18 .r1 1856,
    .addi .r1 .r1 1872 ]

def code : Prog :=
  .seq (.block prologue) (.seq (CC.Limb.Ppc.compiler.code CC.P384.main) (.block epilogue))

/-- The constants table, in `.text` after the function. -/
def constData : List String :=
  ["\t.p2align 6", CC.P384.constLabel ++ ":"] ++
    ((CC.P384.constTable.map (·.toNat)).toChunks 16).map fun c =>
      "\t.byte " ++ String.intercalate "," (c.map toString)

/-- The function is about 190 KiB long, so conditional branches use the long form. -/
def asm : String := (printer constData (long := true)).function name code

end CC.Ppc.P384Wrap
