import ClaudeCrypto.Spec.P384Facts

/-!
# ECDSA signature verification over P-384 (FIPS 186-5, SP 800-186)

This file is the specification that the P-384 implementations are proven
against.  It is meant to be read side by side with

* SP 800-186 §3.2.1.4 (curve P-384: `p`, `n`, `b`, `G`), and
* FIPS 186-5 §6.4.2 (ECDSA signature verification).

The domain parameters `p`, `n`, `b` and the curve are defined in
`Spec/P384Facts.lean` (together with the proofs that `p` and `n` are prime):

```
p = 2^384 − 2^128 − 2^96 + 2^32 − 1
n = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
curve : y² = x³ − 3x + b  over 𝔽_p
```

Points and their addition are Mathlib's (`WeierstrassCurve.Affine.Point`, an
additive commutative group), so the group law itself is not part of what has to
be reviewed.

Byte strings are big-endian, as in FIPS 186-5 / SEC 1.  The inputs are the
public key `Q = x ‖ y` (2 × 48 bytes, uncompressed, without the `04` prefix),
the message digest (48 bytes, e.g. SHA-384; see `hashToInt`), and the signature
`(r, s)` (2 × 48 bytes).
-/

namespace CC.Spec.P384

/-- The field `𝔽_p`. -/
abbrev F := ZMod p

/-- Points of P-384 (including the point at infinity `0`). -/
abbrev Point := curve.toAffine.Point

/-- The base point `G` (SP 800-186 §3.2.1.4). -/
def Gx : ℕ :=
  0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
def Gy : ℕ :=
  0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f

/-- The curve equation `y² = x³ − 3x + b`. -/
def OnCurve (x y : F) : Prop := y ^ 2 = x ^ 3 - 3 * x + (b : F)

instance (x y : F) : Decidable (OnCurve x y) := inferInstanceAs (Decidable (_ = _))

/-- The point `(x, y)`, given that it satisfies the curve equation. -/
def mkPoint (x y : F) (h : OnCurve x y) : Point := .mk ((curve_equation_iff x y).mpr h)

theorem G_on_curve : OnCurve (Gx : F) (Gy : F) := by decide +kernel

def G : Point := mkPoint Gx Gy G_on_curve

/-- Big-endian bytes to an integer. -/
def bytesToNat (bs : List (BitVec 8)) : ℕ := bs.foldl (fun acc x => 256 * acc + x.toNat) 0

/-- Public-key validation (the partial validation of SP 800-186 §D.1.1.2 for a
key given as affine coordinates): both coordinates are integers in `[0, p)` and
the point is on the curve.  Returns the point. -/
def decodePoint (x y : ℕ) : Option Point :=
  if h : x < p ∧ y < p ∧ OnCurve (x : F) (y : F) then some (mkPoint x y h.2.2) else none

/-- FIPS 186-5 §6.4.2, for a public key `Q`, the integer `e` derived from the
message digest (step 3), and a signature `(r, s)`. -/
def verifyCore (Q : Point) (e r s : ℕ) : Bool :=
  -- 1. If r and s are not both integers in the interval [1, n − 1], output INVALID.
  if ¬ (1 ≤ r ∧ r < n ∧ 1 ≤ s ∧ s < n) then false else
  -- 4. Compute s⁻¹ = s^(−1) mod n.
  let w : ZMod n := (s : ZMod n)⁻¹
  -- 5. Compute u = e · s⁻¹ mod n and v = r · s⁻¹ mod n.
  let u : ZMod n := (e : ZMod n) * w
  let v : ZMod n := (r : ZMod n) * w
  -- 6. Compute R₁ = (x_R, y_R) = u·G + v·Q.  If R₁ = 0, output INVALID.
  match (u.val • G + v.val • Q : Point) with
  | .zero => false
  -- 7. Convert x_R to an integer x̄_R; compute r₁ = x̄_R mod n.
  -- 8. If r = r₁, output VALID; otherwise output INVALID.
  | .some xR _ _ => xR.val % n == r

/-- Step 3 for a 384-bit digest (e.g. SHA-384): `e` is the digest as an integer.
(For other digest lengths, callers convert the digest with the leftmost-bits
rule of FIPS 186-5 §6.4.2 step 3 first.) -/
def hashToInt (digest : List (BitVec 8)) : ℕ := bytesToNat digest

/-- ECDSA-P384 verification on byte strings: public key `x ‖ y`, 48-byte
digest, signature `r ‖ s`.  Invalid public keys are rejected. -/
def verify (qx qy digest r s : List (BitVec 8)) : Bool :=
  match decodePoint (bytesToNat qx) (bytesToNat qy) with
  | none => false
  | some Q => verifyCore Q (hashToInt digest) (bytesToNat r) (bytesToNat s)

end CC.Spec.P384
