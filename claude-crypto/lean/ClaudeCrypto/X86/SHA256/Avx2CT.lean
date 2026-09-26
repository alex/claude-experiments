import ClaudeCrypto.X86.SHA256.Avx2
import ClaudeCrypto.X86.Taint

/-! # Constant-time execution of `cc_sha256_blocks_x86_avx2` -/

namespace CC.X86.SHA256Avx2

open CC.X86

/-- Only the pointers and the block count are public. -/
def publicRegs : TState :=
  ((((TState.mk 0 false).setPub .rsp true).setPub .rdi true).setPub .rsi true).setPub .rdx true

theorem analyze_ok : (taint.analyze 4 code publicRegs).isSome = true := by decide +kernel

/-- **Constant time.**  Two runs from states agreeing on `rsp, rdi, rsi, rdx`
(and the symbol addresses) have identical leakage traces (branch decisions and
memory addresses). -/
theorem constant_time : ConstantTime isa (fun _ => True) (taint.Agree publicRegs) code :=
  taint.constantTime_of_analyze 4 code publicRegs analyze_ok _

end CC.X86.SHA256Avx2
