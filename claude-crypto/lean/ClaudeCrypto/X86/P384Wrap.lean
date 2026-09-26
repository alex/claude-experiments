import ClaudeCrypto.P384.Prog
import ClaudeCrypto.Limb.X86
import ClaudeCrypto.X86.Print

/-!
# `cc_p384_verify_x86_bmi2`: the System V wrapper around the P-384 verifier

`int cc_p384_verify_x86_bmi2(const uint8_t pubkey[96], const uint8_t digest[48], const uint8_t sig[96])`

The arguments arrive in `rdi`, `rsi`, `rdx`, which are already IR registers 5, 4
and 0 (`CC.Limb.X86.phys`); the result, IR register 1, is `rax`.  The wrapper
saves the callee-saved registers the IR code uses (`rbx`, `rbp`, `r12`–`r15`),
allocates the frame (IR register 14 = `r15`) on the stack and restores
everything.  The code of `CC.P384.main` sets IR register 13 (`r14`) to the
constants table itself.  Requires BMI2 (`mulx`) and MOVBE.
-/

namespace CC.X86.P384Wrap

def name : String := "cc_p384_verify_x86_bmi2"

/-- Bytes of stack reserved for the frame (`CC.P384.frameSize`, rounded up). -/
def frameBytes : Nat := 1792

theorem frameSize_le : CC.P384.frameSize ≤ frameBytes := by decide

def prologue : List Instr :=
  [.push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15,
   .alu .sub .q .rsp (.imm (BitVec.ofNat 32 frameBytes)), .mov .q .r15 (.reg .rsp)]

def epilogue : List Instr :=
  [.alu .add .q .rsp (.imm (BitVec.ofNat 32 frameBytes)), .pop .r15, .pop .r14, .pop .r13, .pop .r12,
   .pop .rbp, .pop .rbx]

def code : Prog :=
  .seq (.block prologue) (.seq (CC.Limb.X86.compiler.code CC.P384.main) (.block epilogue))

def asm : String :=
  printer.function name code ++ CC.dataSection [(CC.P384.constLabel, CC.P384.constTable)]

end CC.X86.P384Wrap
