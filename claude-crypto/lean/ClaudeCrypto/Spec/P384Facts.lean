import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import ClaudeCrypto.Spec.P384Cert

/-!
# P-384: facts needed to *state* the specification

The domain parameters, and proofs that `p` and `n` are prime and that the curve
is elliptic.  None of this needs to be reviewed: the definitions here are
restated verbatim in `Spec/P384.lean`, and the proofs are checked by Lean.
-/

namespace CC.Spec.P384

/-- The field prime `p = 2^384 − 2^128 − 2^96 + 2^32 − 1` (SP 800-186 §3.2.1.4). -/
def p : ℕ := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The order `n` of the base point. -/
def n : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

/-- The coefficient `b`. -/
def b : ℕ :=
  0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef

/-- Proven with the Pratt certificate `Pratt.pCert`, checked by the kernel. -/
theorem p_prime : Nat.Prime p := Pratt.checkCert_sound p Pratt.pCert (by decide +kernel)

/-- Proven with the Pratt certificate `Pratt.nCert`, checked by the kernel. -/
theorem n_prime : Nat.Prime n := Pratt.checkCert_sound n Pratt.nCert (by decide +kernel)

instance : Fact (Nat.Prime p) := ⟨p_prime⟩
instance : Fact (Nat.Prime n) := ⟨n_prime⟩

/-- `y² = x³ − 3x + b` over `𝔽_p`. -/
def curve : WeierstrassCurve (ZMod p) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -3, a₆ := b }

theorem curve_Δ_ne_zero : curve.Δ ≠ 0 := by decide +kernel

instance curve_isElliptic : curve.IsElliptic := ⟨isUnit_iff_ne_zero.2 curve_Δ_ne_zero⟩

theorem curve_equation_iff (x y : ZMod p) :
    curve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 3 * x + (b : ZMod p) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

end CC.Spec.P384
