import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Viewing wide bit-vectors as vectors of lanes

`BitVec.lanes n f` packs `n` lanes `f 0, …, f (n-1)` (lane 0 least
significant) into one bit-vector; `BitVec.lane w x i` extracts lane `i` of
width `w`.  SIMD instruction semantics are defined lane-wise with these.
-/

namespace BitVec

/-- Lane `i` (of width `w`) of `x`. -/
def lane {n : Nat} (w : Nat) (x : BitVec n) (i : Nat) : BitVec w := x.extractLsb' (w * i) w

/-- Pack `n` lanes of width `w`, lane `0` least significant. -/
def lanes {w : Nat} : (n : Nat) → (Nat → BitVec w) → BitVec (w * n)
  | 0, _ => 0#0
  | n + 1, f => (lanes n (fun i => f (i + 1)) ++ f 0 : BitVec (w * n + w))

theorem getLsbD_lanes {w : Nat} (n : Nat) (f : Nat → BitVec w) (j : Nat) :
    (lanes n f).getLsbD j = (decide (j < w * n) && (f (j / w)).getLsbD (j % w)) := by
  induction n generalizing f j with
  | zero => simp [lanes]
  | succ n ih =>
    simp only [lanes, getLsbD_append, ih]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw; simp
    by_cases h : j < w
    · simp only [h, ite_true]
      have : j / w = 0 := Nat.div_eq_of_lt h
      have h2 : j % w = j := Nat.mod_eq_of_lt h
      rw [this, h2]
      have : j < w * (n + 1) := by nlinarith
      simp only [this, decide_true, Bool.true_and]
    · simp only [h, ite_false]
      have hjw : w ≤ j := Nat.le_of_not_lt h
      rw [← Nat.div_eq_sub_div hw hjw, ← Nat.mod_eq_sub_mod hjw]
      congr 1
      simp only [decide_eq_decide]
      rw [Nat.mul_succ]; omega

theorem lane_lanes {w : Nat} (n : Nat) (f : Nat → BitVec w) (i : Nat) (hi : i < n) :
    lane w (lanes n f) i = f i := by
  apply eq_of_getLsbD_eq
  intro j hj
  rw [lane, getLsbD_extractLsb', getLsbD_lanes]
  have h1 : w * i + j < w * n := by nlinarith
  have h2 : (w * i + j) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj]; simp
  have h3 : (w * i + j) % w = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp [hj, h1, h2, h3]

/-- Two vectors are equal if all their lanes are. -/
theorem eq_of_lanes {w n : Nat} (x y : BitVec (w * n)) (h : ∀ i < n, lane w x i = lane w y i) : x = y := by
  apply eq_of_getLsbD_eq
  intro j hj
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simp at hj
  have hq : j / w < n := by
    rw [Nat.div_lt_iff_lt_mul hw]; linarith [Nat.mul_comm w n]
  have := congrArg (fun v => v.getLsbD (j % w)) (h (j / w) hq)
  simp only [lane, getLsbD_extractLsb'] at this
  have hm : j % w < w := Nat.mod_lt _ hw
  simp only [hm, decide_true, Bool.true_and] at this
  rwa [Nat.div_add_mod] at this

end BitVec
