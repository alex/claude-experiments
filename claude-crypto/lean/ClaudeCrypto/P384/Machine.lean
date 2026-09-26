import ClaudeCrypto.P384.Main
import ClaudeCrypto.X86.P384Main
import ClaudeCrypto.Arm.P384Main
import ClaudeCrypto.Ppc.P384Main

/-!
# ECDSA-P384 verification: the machine-code theorems

`CC.P384.main_ok` (the IR program computes `Spec.P384.verify`) transported
through the verified compilers and the function wrappers.
-/

namespace CC.P384

/-- x86-64: `cc_p384_verify_x86_bmi2` returns `verify` of its inputs (see
`CC.X86.P384Wrap.correct_of` for the preconditions). -/
theorem x86_correct : type_of% (CC.X86.P384Wrap.correct_of main_ok) := CC.X86.P384Wrap.correct_of main_ok

/-- AArch64: `cc_p384_verify_aarch64` returns `verify` of its inputs (see
`CC.Arm.P384Wrap.correct_of` for the preconditions). -/
theorem arm_correct : type_of% (CC.Arm.P384Wrap.correct_of main_ok) := CC.Arm.P384Wrap.correct_of main_ok

/-- ppc64le: `cc_p384_verify_ppc64le` returns `verify` of its inputs (see
`CC.Ppc.P384Wrap.correct_of` for the preconditions). -/
theorem ppc_correct : type_of% (CC.Ppc.P384Wrap.correct_of main_ok) := CC.Ppc.P384Wrap.correct_of main_ok

end CC.P384
