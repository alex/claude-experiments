import ClaudeCrypto.Spec.SHA256

/-!
# Proof-oriented reformulations of the SHA-256 specification

Architecture-independent lemmas used by all the implementation proofs.
Nothing in this file needs to be reviewed to trust the results: it only
proves facts about `Spec/SHA256.lean`.
-/

namespace CC.Spec.SHA256

/-- The message schedule as a recursive function. -/
def Wt (M : List Word) (t : Nat) : Word :=
  if t < 16 then M[t]! else
    sigma1 (Wt M (t - 2)) + Wt M (t - 7) + sigma0 (Wt M (t - 15)) + Wt M (t - 16)
termination_by t
decreasing_by all_goals omega

theorem Wt_lt (M : List Word) (t : Nat) (h : t < 16) : Wt M t = M[t]! := by
  rw [Wt]; simp [h]

theorem Wt_ge (M : List Word) (t : Nat) (h : 16 ≤ t) :
    Wt M t = sigma1 (Wt M (t - 2)) + Wt M (t - 7) + sigma0 (Wt M (t - 15)) + Wt M (t - 16) := by
  rw [Wt]; simp [show ¬ t < 16 by omega]

theorem schedule_prefix (M : List Word) (hM : M.length = 16) (k : Nat) :
    ((List.range k).foldl
      (fun W t => W ++ [sigma1 W[t + 14]! + W[t + 9]! + sigma0 W[t + 1]! + W[t]!]) M) =
    (List.range (16 + k)).map (Wt M) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    apply List.ext_getElem
    · simp [hM]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [Wt_lt _ _ (by simp [hM] at h1; omega)]
      simp [getElem!_pos, h1]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show 16 + (k + 1) = (16 + k) + 1 by omega, List.range_succ, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [Wt_ge _ _ (by omega)]
    have g : ∀ i, i < 16 + k → ((List.range (16 + k)).map (Wt M))[i]! = Wt M i := by
      intro i hi; simp [getElem!_pos, hi]
    rw [g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega)]
    congr <;> omega

theorem schedule_getElem (M : List Word) (hM : M.length = 16) (t : Nat) (ht : t < 64) :
    (schedule M)[t]! = Wt M t := by
  rw [schedule, schedule_prefix M hM]
  simp [getElem!_pos, show t < 16 + 48 by omega]

/-- The initial working variables for hash value `H`. -/
def initVars (H : List Word) : Vars := ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩

/-- The working variables after `t` rounds of compressing block `M` into `H`. -/
def varsAt (H M : List Word) (t : Nat) : Vars :=
  (List.range t).foldl (fun v i => round v K[i]! (schedule M)[i]!) (initVars H)

theorem varsAt_zero (H M : List Word) : varsAt H M 0 = initVars H := rfl

theorem varsAt_succ (H M : List Word) (hM : M.length = 16) (t : Nat) (ht : t < 64) :
    varsAt H M (t + 1) = round (varsAt H M t) K[t]! (Wt M t) := by
  rw [varsAt, List.range_succ, List.foldl_append, ← schedule_getElem M hM t ht]; rfl

theorem compress_eq (H M : List Word) :
    compress H M =
      [(varsAt H M 64).a + H[0]!, (varsAt H M 64).b + H[1]!, (varsAt H M 64).c + H[2]!,
       (varsAt H M 64).d + H[3]!, (varsAt H M 64).e + H[4]!, (varsAt H M 64).f + H[5]!,
       (varsAt H M 64).g + H[6]!, (varsAt H M 64).h + H[7]!] := rfl

/-! ## Messages as sequences of blocks -/

/-- Word `j` of block `i` of a byte string. -/
def msgWord (msg : List (BitVec 8)) (i j : Nat) : Word :=
  wordBE msg[64 * i + 4 * j]! msg[64 * i + 4 * j + 1]! msg[64 * i + 4 * j + 2]! msg[64 * i + 4 * j + 3]!

/-- Block `i` of a byte string, as sixteen words. -/
def msgBlock (msg : List (BitVec 8)) (i : Nat) : List Word := (List.range 16).map (msgWord msg i)

theorem msgBlock_length (msg : List (BitVec 8)) (i : Nat) : (msgBlock msg i).length = 16 := by
  simp [msgBlock]

theorem msgBlock_getElem (msg : List (BitVec 8)) (i j : Nat) (hj : j < 16) :
    (msgBlock msg i)[j]! = msgWord msg i j := by
  simp [msgBlock, getElem!_pos, hj]

theorem toWords_append4 (b0 b1 b2 b3 : BitVec 8) (l : List (BitVec 8)) :
    toWords (b0 :: b1 :: b2 :: b3 :: l) = wordBE b0 b1 b2 b3 :: toWords l := by
  rw [toWords]

theorem toWords_length (l : List (BitVec 8)) : (toWords l).length = l.length / 4 := by
  induction l using toWords.induct with
  | case1 b0 b1 b2 b3 rest ih => rw [toWords_append4]; simp [ih]; omega
  | case2 l h =>
    rw [toWords.eq_def]
    match l, h with
    | [], _ => simp
    | [_], _ => simp
    | [_, _], _ => simp
    | [_, _, _], _ => simp
    | _ :: _ :: _ :: _ :: _, h => exact absurd rfl (h _ _ _ _ _)

theorem toWords_getElem (l : List (BitVec 8)) (i : Nat) (hi : 4 * i + 3 < l.length) :
    (toWords l)[i]! = wordBE l[4 * i]! l[4 * i + 1]! l[4 * i + 2]! l[4 * i + 3]! := by
  induction l using toWords.induct generalizing i with
  | case1 b0 b1 b2 b3 rest ih =>
    rw [toWords_append4]
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem!_cons_succ]
      rw [ih i (by simp at hi; omega)]
      simp only [show 4 * (i + 1) = 4 * i + 3 + 1 by omega, show 4 * i + 3 + 1 + 1 = 4 * i + 1 + 3 + 1 by omega,
        show 4 * i + 3 + 1 + 2 = 4 * i + 2 + 3 + 1 by omega, show 4 * i + 3 + 1 + 3 = 4 * i + 3 + 3 + 1 by omega,
        List.getElem!_cons_succ]
  | case2 l h =>
    exfalso
    match l, h with
    | [], _ => simp at hi
    | [_], _ => simp at hi
    | [_, _], _ => simp at hi
    | [_, _, _], _ => simp at hi
    | _ :: _ :: _ :: _ :: _, h => exact absurd rfl (h _ _ _ _ _)

theorem chunks_eq {α : Type} (n : Nat) (l : List α) :
    chunks n l = if 0 < n ∧ l ≠ [] then l.take n :: chunks n (l.drop n) else [] := by
  rw [chunks]; split <;> simp_all

theorem chunks_blocks {α : Type} (l : List α) (k : Nat) (hl : l.length = 16 * k) :
    chunks 16 l = (List.range k).map (fun i => (l.drop (16 * i)).take 16) := by
  induction k generalizing l with
  | zero => rw [chunks_eq]; simp at hl; simp [hl]
  | succ k ih =>
    rw [chunks_eq, if_pos ⟨by omega, by intro h; simp [h] at hl⟩, ih _ (by simp [hl]; omega)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    simp only [List.drop_drop, List.map_inj_left, List.mem_range, Function.comp]
    intro a _; congr 2; simp only [Nat.succ_eq_add_one]; ring

/-- A message that is a whole number of blocks parses as `msgBlock`s. -/
theorem blocks_eq (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    chunks 16 (toWords msg) = (List.range n).map (msgBlock msg) := by
  rw [chunks_blocks (toWords msg) n (by rw [toWords_length, hl]; omega)]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  apply List.ext_getElem
  · simp [toWords_length, hl, msgBlock]; omega
  · intro j h1 h2
    simp only [msgBlock, List.getElem_map, List.getElem_range, msgWord]
    simp only [List.length_take, List.length_drop, toWords_length, hl] at h1
    have : (List.take 16 (List.drop (16 * i) (toWords msg)))[j] = (toWords msg)[16 * i + j]! := by
      rw [getElem!_pos _ _ (by rw [toWords_length, hl]; omega)]
      simp [List.getElem_take, List.getElem_drop]
    rw [this, toWords_getElem _ _ (by rw [hl]; omega)]
    congr 1 <;> congr 1 <;> omega

/-- The hash value after compressing the first `i` blocks of `msg` into `H`. -/
def stateAfter (H : List Word) (msg : List (BitVec 8)) (i : Nat) : List Word :=
  (List.range i).foldl (fun H j => compress H (msgBlock msg j)) H

theorem stateAfter_succ (H : List Word) (msg : List (BitVec 8)) (i : Nat) :
    stateAfter H msg (i + 1) = compress (stateAfter H msg i) (msgBlock msg i) := by
  rw [stateAfter, List.range_succ, List.foldl_append]; rfl

theorem blocks_foldl (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    (chunks 16 (toWords msg)).foldl compress H = stateAfter H msg n := by
  rw [blocks_eq msg n hl, stateAfter, List.foldl_map]

end CC.Spec.SHA256
