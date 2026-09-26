import ClaudeCrypto.Ppc.SHA256.P8Phases

/-!
# One round of the ppc64le SHA-256 code, semantically

`step_vars`: a `stepCode r` performs one FIPS 180-4 round on the working
variables held in `word[0]` of the rotating registers `varReg r k`;
`stepPost_getV`/`stepPost_same`: it changes nothing else but its temporaries.
-/

namespace CC.Ppc.SHA256P8

open CC.Spec.SHA256

set_option linter.unusedSimpArgs false

/-- `s` and `s'` agree on everything but the vector registers and CR0. -/
structure Same (s s' : State) : Prop where
  g : s'.g = s.g
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  labels : s'.labels = s.labels
  lr : s'.lr = s.lr
  vsr : s'.vsr = s.vsr
  cr1to7 : s'.cr1to7 = s.cr1to7

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {s s' s'' : State} (h : Same s s') (h' : Same s' s'') : Same s s'' :=
  ⟨h'.g.trans h.g, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.labels.trans h.labels,
    h'.lr.trans h.lr, h'.vsr.trans h.vsr, h'.cr1to7.trans h.cr1to7⟩

theorem Same.setV (s : State) (r : VReg) (x : BitVec 128) : Same s (s.setV r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The working variables `v` in `word[0]` of the registers of round `t`. -/
def VarsAt (s : State) (t : Nat) (v : Vars) : Prop :=
  VarsW (s.getV (varReg t 0)) (s.getV (varReg t 1)) (s.getV (varReg t 2)) (s.getV (varReg t 3))
    (s.getV (varReg t 4)) (s.getV (varReg t 5)) (s.getV (varReg t 6)) (s.getV (varReg t 7)) v

theorem varReg_mod (t k : Nat) : varReg t k = varReg (t % 8) k := by
  unfold varReg; rw [Nat.mod_mod]

theorem VarsAt_mod (s : State) (t : Nat) (v : Vars) : VarsAt s t v ↔ VarsAt s (t % 8) v := by
  simp only [VarsAt, ← varReg_mod]

/-- The vector registers a step writes. -/
def stepTouched : VReg → Bool
  | .v0 | .v1 | .v2 | .v3 | .v4 | .v5 | .v6 | .v7 | .v13 | .v14 | .v15 => true
  | _ => false

theorem Same.setV' {s s' : State} (h : Same s s') (r : VReg) (x : BitVec 128) :
    Same s (s'.setV r x) := h.trans (Same.setV _ _ _)

theorem roundPost_same (r : Nat) (x : BitVec 128) (s : State) : Same s (roundPost r x s) :=
  ((((Same.refl s).setV' _ _).setV' _ _).setV' _ _).setV' _ _

theorem stepPost_same (r : Nat) (s : State) : Same s (stepPost r s) := by
  unfold stepPost
  split
  · exact roundPost_same _ _ _
  · exact (Same.setV _ _ _).trans (roundPost_same _ _ _)

theorem stepPost_getV (r : Nat) (hr : r < 8) (s : State) (x : VReg) (hx : stepTouched x = false) :
    (stepPost r s).getV x = s.getV x := by
  have h : ∀ y, stepTouched y = true → x ≠ y := fun y hy e => by subst e; rw [hx] at hy; cases hy
  have h0 := h .v0 rfl; have h1 := h .v1 rfl; have h2 := h .v2 rfl; have h3 := h .v3 rfl
  have h4 := h .v4 rfl; have h5 := h .v5 rfl; have h6 := h .v6 rfl; have h7 := h .v7 rfl
  have h13 := h .v13 rfl; have h14 := h .v14 rfl; have h15 := h .v15 rfl
  interval_cases r <;>
    simp [stepPost, roundPost, kwOf, varReg, State.getV_setV, h0, h1, h2, h3, h4, h5, h6, h7, h13,
      h14, h15]

theorem kwOf_word (r : Nat) (hr : r < 8) (s : State) :
    word (kwOf r s) 0 = word (s.getV .v12) (r % 4) := by
  have := word_vsldoi_self (s.getV .v12)
  interval_cases r <;> simp [kwOf, this]

/-- One step is one round of the specification. -/
theorem step_vars (r : Nat) (hr : r < 8) (s : State) (v : Vars) (k w : Word) (hv : VarsAt s r v)
    (hkw : word (s.getV .v12) (r % 4) = k + w) :
    VarsAt (stepPost r s) (r + 1) (Spec.SHA256.round v k w) := by
  have hkw' := (kwOf_word r hr s).trans hkw
  have key := round_word _ _ _ _ _ _ _ _ (kwOf r s) v k w hv hkw'
  interval_cases r <;>
  · simp only [VarsAt, stepPost, roundPost, varReg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
      ite_true, ite_false, reduceIte, State.getV_setV, reduceCtorEq, Nat.zero_mod] at key ⊢
    exact key

end CC.Ppc.SHA256P8
