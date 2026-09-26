import ClaudeCrypto.X86.SHA256.Scalar
import ClaudeCrypto.X86.Taint

/-!
# Constant-time: `cc_sha256_blocks_x86_scalar`

Only `rsp`, `rdi` (hash-state pointer), `rsi` (message pointer) and `rdx`
(block count) are public.  The taint analysis accepts the function, so its
control flow and memory-access pattern are independent of the message and of
the hash state (and of every other register).
-/

namespace CC.X86.SHA256Scalar

/-- Initially public: `rsp`, `rdi`, `rsi`, `rdx`. -/
def publicRegs : TState :=
  ((((TState.mk 0 false).setPub .rsp true).setPub .rdi true).setPub .rsi true).setPub .rdx true

theorem analyze_ok : (taint.analyze 4 code publicRegs).isSome = true := by decide +kernel

/-- **Constant time.**  Two runs from states agreeing on `rsp, rdi, rsi, rdx`
have identical leakage traces (branch decisions and memory addresses). -/
theorem constant_time : ConstantTime isa (fun _ => True) (taint.Agree publicRegs) code :=
  taint.constantTime_of_analyze 4 code publicRegs analyze_ok _

end CC.X86.SHA256Scalar
