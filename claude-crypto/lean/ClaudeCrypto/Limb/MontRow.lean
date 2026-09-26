import ClaudeCrypto.Limb.Row
import ClaudeCrypto.Limb.Small
import ClaudeCrypto.Limb.MontMath

/-!
# One round of Montgomery multiplication in the IR

Register use: `r0` multiplicand, `r1..r8` the 8 rotating accumulator limbs
(`rot i k` is limb `k` in round `i`), `r9` scratch, `r10`/`r11` carry words,
`r12` zero, `r13` constants pointer (modulus and `-N⁻¹ mod 2^64`), `r14` frame
pointer (operands).
-/

namespace CC.Limb

/-- Accumulator limb `k` in round `i`. -/
def rot (i k : Nat) : Var := ⟨(i + k) % 8 + 1, by omega⟩

theorem rot_val (i k : Nat) : (rot i k).val = (i + k) % 8 + 1 := rfl

theorem rot_inj (i j k : Nat) (hj : j < 8) (hk : k < 8) (h : rot i j = rot i k) : j = k := by
  have := congrArg Fin.val h; simp only [rot_val] at this; omega

theorem rot_ne (i k : Nat) (v : Var) (hv : v.val = 0 ∨ 9 ≤ v.val) : rot i k ≠ v := by
  intro h; have := congrArg Fin.val h; simp only [rot_val] at this; omega

theorem rot_succ (i k : Nat) : rot (i + 1) k = rot i (k + 1) := by
  apply Fin.ext; simp only [rot_val]; omega

def montRow (offA offB offN offMp i : Nat) : List Instr :=
  [.ld 0 14 (offB + 8 * i)] ++ macRow (rot i) 14 (fun j => offA + 8 * j) 10 11 9 12 6 ++
    addTop (rot i 6) 11 (rot i 7) 12 ++ qCompute (rot i 0) 13 offMp 10 11 9 ++
    macRow (rot i) 13 (fun j => offN + 8 * j) 10 11 9 12 6 ++ addTop (rot i 6) 11 (rot i 7) 12

theorem rowRegs (i : Nat) (base : Var) (hb : base.val = 13 ∨ base.val = 14) :
    RowRegs (rot i) base 10 11 9 12 6 := by
  have hne : ∀ v : Var, v.val ≠ base.val → v ≠ base := fun v h e => h (congrArg Fin.val e)
  refine ⟨fun a ha b hb' h => rot_inj i a b (by omega) (by omega) h, fun j hj => ?_, by decide,
    ⟨by decide, by decide, by decide, hne _ (by simp; omega)⟩, ⟨by decide, by decide, by decide, hne _ (by simp; omega)⟩,
    ⟨by decide, by decide, hne _ (by simp; omega)⟩⟩
  · refine ⟨rot_ne _ _ _ (by simp), rot_ne _ _ _ (by simp), rot_ne _ _ _ (by simp), rot_ne _ _ _ (by simp),
      rot_ne _ _ _ (by simp), rot_ne _ _ _ (by omega)⟩

end CC.Limb
