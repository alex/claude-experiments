import ClaudeCrypto.Ppc.SHA256.P8
import ClaudeCrypto.Ppc.Taint

/-!
# Constant time: `cc_sha256_blocks_ppc64le`

Only `r3` (hash-value pointer), `r4` (message pointer) and `r5` (block count)
are public (plus, as always, the link-time addresses of the program's data
labels).  The taint analysis accepts the function, so its control flow and
memory-access pattern are independent of the message, of the hash value, and
of every other register.
-/

namespace CC.Ppc.SHA256P8

/-- Initially public: `r3`, `r4`, `r5`. -/
def publicRegs : TState :=
  (((TState.mk 0 false).setPub .r3 true).setPub .r4 true).setPub .r5 true

theorem analyze_ok : (taint.analyze 4 code publicRegs).isSome = true := by decide +kernel

/-- **Constant time.**  Two runs from states agreeing on `r3, r4, r5` (and on
the addresses of data labels) have identical leakage traces (branch decisions
and memory addresses). -/
theorem constant_time : ConstantTime isa (fun _ => True) (taint.Agree publicRegs) code :=
  taint.constantTime_of_analyze 4 code publicRegs analyze_ok _

end CC.Ppc.SHA256P8
