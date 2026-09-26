import ClaudeCrypto.Arm.SHA256.Ce
import ClaudeCrypto.Arm.Taint

/-!
# Constant time: `cc_sha256_blocks_arm`

Only `x0` (hash-value pointer), `x1` (message pointer) and `x2` (block count)
are public (plus, as always, the link-time addresses of the program's data
labels).  The taint analysis accepts the function, so its control flow and
memory-access pattern are independent of the message, of the hash value, and
of every other register.
-/

namespace CC.Arm.SHA256Ce

/-- Initially public: `x0`, `x1`, `x2`. -/
def publicRegs : TState :=
  (((TState.mk 0 false).setPub .x0 true).setPub .x1 true).setPub .x2 true

theorem analyze_ok : (taint.analyze 4 code publicRegs).isSome = true := by decide +kernel

/-- **Constant time.**  Two runs from states agreeing on `x0, x1, x2` (and on
the addresses of data labels) have identical leakage traces (branch decisions
and memory addresses). -/
theorem constant_time : ConstantTime isa (fun _ => True) (taint.Agree publicRegs) code :=
  taint.constantTime_of_analyze 4 code publicRegs analyze_ok _

end CC.Arm.SHA256Ce
