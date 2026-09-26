import ClaudeCrypto.P384.Prog
import ClaudeCrypto.Limb.Arm
import ClaudeCrypto.Arm.Print

/-!
# `cc_p384_verify_aarch64`: the AAPCS64 wrapper around the P-384 verifier

`int cc_p384_verify_aarch64(const uint8_t pubkey[96], const uint8_t digest[48], const uint8_t sig[96])`

The arguments arrive in `x0`, `x1`, `x2` and are moved to IR registers 5, 4
and 0 (`x5`, `x4`, `x0`: `CC.Limb.Arm.phys v = X<v>`); the frame (IR register
14 = `x14`) is allocated on the stack; the result, IR register 1 (`x1`), is
returned in `x0`.  The compiled IR code only uses the caller-saved registers
`x0`–`x14` and `x16` and never touches `SP`, so nothing needs to be saved.  The
code of `CC.P384.main` sets IR register 13 (`x13`) to the constants table (with
`adr`), which is emitted in `.text` right after the function.
-/

namespace CC.Arm.P384Wrap

def name : String := "cc_p384_verify_aarch64"

/-- Bytes of stack reserved for the frame (`CC.P384.frameSize`, rounded up to keep `SP`
16-byte aligned). -/
def frameBytes : Nat := 1792

theorem frameSize_le : CC.P384.frameSize ≤ frameBytes := by decide
theorem frameBytes_aligned : frameBytes % 16 = 0 := by decide

def prologue : List Instr :=
  [.mov .x5 .x0, .mov .x4 .x1, .mov .x0 .x2, .subsp frameBytes, .movsp .x14]

def epilogue : List Instr := [.mov .x0 .x1, .addsp frameBytes]

def code : Prog :=
  .seq (.block prologue) (.seq (CC.Limb.Arm.compiler.code CC.P384.main) (.block epilogue))

/-- The constants table, in `.text` after the function (so that `adr` reaches it). -/
def constData : List String :=
  ["\t.p2align 6", CC.P384.constLabel ++ ":"] ++
    ((CC.P384.constTable.map (·.toNat)).toChunks 16).map fun c =>
      "\t.byte " ++ String.intercalate "," (c.map toString)

def asm : String := (printer constData).function name code

end CC.Arm.P384Wrap
