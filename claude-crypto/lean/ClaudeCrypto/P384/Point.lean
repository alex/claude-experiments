import ClaudeCrypto.Limb.FProg
import ClaudeCrypto.Spec.P384Jacobian

/-!
# P-384 point arithmetic as field programs

The formulas of `Spec/P384Jacobian.lean` written as `mul/add/sub` programs on
frame slots, and proofs that the programs' meaning is exactly those formulas.
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- Doubling in place: `(X, Y, Z)` in slots `x, y, z`; temporaries `t, t+1, …, t+5`. -/
def dblProg (x y z t : Nat) : List FOp :=
  let δ := t; let γ := t + 1; let β := t + 2; let a := t + 3; let u := t + 4; let w := t + 5
  [ .mul δ z z, .mul γ y y, .mul β x γ, .sub a x δ, .add u x δ, .mul a a u, .add u a a, .add a u a,
    .add u y z, .mul u u u, .sub u u γ, .sub z u δ,
    .mul u a a, .add δ β β, .add δ δ δ, .add w δ δ, .sub x u w,
    .sub δ δ x, .mul δ a δ, .mul γ γ γ, .add γ γ γ, .add γ γ γ, .add γ γ γ, .sub y δ γ ]

theorem dbl_run (v : Nat → F) :
    let r := FProg.run (dblProg 0 1 2 6) v
    let X := v 0; let Y := v 1; let Z := v 2
    let δ := Z ^ 2
    let γ := Y ^ 2
    let β := X * γ
    let α := 3 * (X - δ) * (X + δ)
    let X₃ := α ^ 2 - 8 * β
    let Z₃ := (Y + Z) ^ 2 - γ - δ
    let Y₃ := α * (4 * β - X₃) - 8 * γ ^ 2
    r 0 = X₃ ∧ r 1 = Y₃ ∧ r 2 = Z₃ := by
  intro r X Y Z δ γ β α X₃ Z₃ Y₃
  simp only [r, dblProg, FProg.run, FOp.run, Function.update_apply]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, X, Y, Z, X₃, Y₃, Z₃, α, β, γ, δ]
  refine ⟨by ring, by ring, by ring⟩

/-- madd-2007-bl, first part: `t = Z1Z1, t+1 = H, t+2 = r` for `(X1,Y1,Z1)` in `x,y,z`, `(x2,y2)` in `a,b`. -/
def maddPre (x y z a b t : Nat) : List FOp :=
  [ .mul t z z, .mul (t + 1) a t, .mul (t + 2) z t, .mul (t + 2) b (t + 2), .sub (t + 1) (t + 1) x,
    .sub (t + 2) (t + 2) y, .add (t + 2) (t + 2) (t + 2) ]

/-- madd-2007-bl, second part (after `maddPre`): the sum into `x, y, z`. -/
def maddPost (x y z t : Nat) : List FOp :=
  let Z1Z1 := t; let H := t + 1; let r := t + 2; let HH := t + 3; let V := t + 4; let J := t + 5; let u := t + 6
  [ .mul HH H H, .add V HH HH, .add V V V, .mul J H V, .mul V x V,
    .add u z H, .mul u u u, .sub u u Z1Z1, .sub z u HH,
    .mul x r r, .sub x x J, .sub x x V, .sub x x V,
    .sub V V x, .mul V r V, .mul HH y J, .add HH HH HH, .sub y V HH ]

theorem maddPre_run (v : Nat → F) :
    let r := FProg.run (maddPre 0 1 2 3 4 5) v
    let X₁ := v 0; let Y₁ := v 1; let Z₁ := v 2; let x₂ := v 3; let y₂ := v 4
    let Z1Z1 := Z₁ ^ 2
    let U₂ := x₂ * Z1Z1
    let S₂ := y₂ * Z₁ * Z1Z1
    r 5 = Z1Z1 ∧ r 6 = U₂ - X₁ ∧ r 7 = 2 * (S₂ - Y₁) ∧ (∀ i < 5, r i = v i) := by
  intro r X₁ Y₁ Z₁ x₂ y₂ Z1Z1 U₂ S₂
  simp only [r, maddPre, FProg.run, FOp.run, Function.update_apply]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, X₁, Y₁, Z₁, x₂, y₂, Z1Z1, U₂, S₂]
  refine ⟨by ring, by ring, by ring, fun i hi => ?_⟩
  simp only [show i ≠ 7 by omega, show i ≠ 6 by omega, show i ≠ 5 by omega, reduceIte]

theorem maddPost_run (v : Nat → F) :
    let r := FProg.run (maddPost 0 1 2 5) v
    let X₁ := v 0; let Y₁ := v 1; let Z₁ := v 2; let Z1Z1 := v 5; let H := v 6; let rr := v 7
    let HH := H ^ 2
    let I := 4 * HH
    let J := H * I
    let V := X₁ * I
    let X₃ := rr ^ 2 - J - 2 * V
    let Y₃ := rr * (V - X₃) - 2 * Y₁ * J
    let Z₃ := (Z₁ + H) ^ 2 - Z1Z1 - HH
    r 0 = X₃ ∧ r 1 = Y₃ ∧ r 2 = Z₃ := by
  intro r X₁ Y₁ Z₁ Z1Z1 H rr HH I J V X₃ Y₃ Z₃
  simp only [r, maddPost, FProg.run, FOp.run, Function.update_apply]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, X₁, Y₁, Z₁, Z1Z1, H, rr, HH, I, J, V, X₃, Y₃, Z₃]
  refine ⟨by ring, by ring, by ring⟩

/-- add-2007-bl, first part: `(X1,Y1,Z1)` in `x,y,z`, `(X2,Y2,Z2)` in `a,b,c`;
`t = Z1Z1, t+1 = Z2Z2, t+2 = U1, t+3 = S1, t+4 = H, t+5 = r`. -/
def addPre (x y z a b c t : Nat) : List FOp :=
  [ .mul t z z, .mul (t + 1) c c, .mul (t + 2) x (t + 1), .mul (t + 4) a t,
    .mul (t + 3) c (t + 1), .mul (t + 3) y (t + 3), .mul (t + 5) z t, .mul (t + 5) b (t + 5),
    .sub (t + 4) (t + 4) (t + 2), .sub (t + 5) (t + 5) (t + 3), .add (t + 5) (t + 5) (t + 5) ]

/-- add-2007-bl, second part: the sum into `x, y, z`. -/
def addPost (x y z c t : Nat) : List FOp :=
  let Z1Z1 := t; let Z2Z2 := t + 1; let U1 := t + 2; let S1 := t + 3; let H := t + 4; let r := t + 5
  let I := t + 6; let J := t + 7; let u := t + 8
  [ .add I H H, .mul I I I, .mul J H I, .mul I U1 I,
    .add u z c, .mul u u u, .sub u u Z1Z1, .sub u u Z2Z2, .mul z u H,
    .mul x r r, .sub x x J, .sub x x I, .sub x x I,
    .sub I I x, .mul I r I, .mul u S1 J, .add u u u, .sub y I u ]

theorem addPre_run (v : Nat → F) :
    let r := FProg.run (addPre 0 1 2 3 4 5 6) v
    let X₁ := v 0; let Y₁ := v 1; let Z₁ := v 2; let X₂ := v 3; let Y₂ := v 4; let Z₂ := v 5
    let Z1Z1 := Z₁ ^ 2
    let Z2Z2 := Z₂ ^ 2
    let U₁ := X₁ * Z2Z2
    let U₂ := X₂ * Z1Z1
    let S₁ := Y₁ * Z₂ * Z2Z2
    let S₂ := Y₂ * Z₁ * Z1Z1
    r 6 = Z1Z1 ∧ r 7 = Z2Z2 ∧ r 8 = U₁ ∧ r 9 = S₁ ∧ r 10 = U₂ - U₁ ∧ r 11 = 2 * (S₂ - S₁) ∧
      (∀ i < 6, r i = v i) := by
  intro r X₁ Y₁ Z₁ X₂ Y₂ Z₂ Z1Z1 Z2Z2 U₁ U₂ S₁ S₂
  simp only [r, addPre, FProg.run, FOp.run, Function.update_apply]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, X₁, Y₁, Z₁, X₂, Y₂, Z₂, Z1Z1, Z2Z2, U₁, U₂, S₁, S₂]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, fun i hi => ?_⟩
  simp only [show i ≠ 11 by omega, show i ≠ 10 by omega, show i ≠ 9 by omega, show i ≠ 8 by omega,
    show i ≠ 7 by omega, show i ≠ 6 by omega, reduceIte]

theorem addPost_run (v : Nat → F) :
    let r := FProg.run (addPost 0 1 2 5 6) v
    let Y₁ := v 1; let Z₁ := v 2; let Z₂ := v 5
    let Z1Z1 := v 6; let Z2Z2 := v 7; let U₁ := v 8; let S₁ := v 9; let H := v 10; let rr := v 11
    let I := (2 * H) ^ 2
    let J := H * I
    let V := U₁ * I
    let X₃ := rr ^ 2 - J - 2 * V
    let Y₃ := rr * (V - X₃) - 2 * S₁ * J
    let Z₃ := ((Z₁ + Z₂) ^ 2 - Z1Z1 - Z2Z2) * H
    r 0 = X₃ ∧ r 1 = Y₃ ∧ r 2 = Z₃ := by
  intro r Y₁ Z₁ Z₂ Z1Z1 Z2Z2 U₁ S₁ H rr I J V X₃ Y₃ Z₃
  simp only [r, addPost, FProg.run, FOp.run, Function.update_apply]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, Y₁, Z₁, Z₂, Z1Z1, Z2Z2, U₁, S₁, H, rr, I, J, V,
    X₃, Y₃, Z₃]
  refine ⟨by ring, by ring, by ring⟩

end CC.P384
