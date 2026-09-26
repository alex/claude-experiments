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

theorem cin6 : cin 12 10 11 6 = 11 := rfl

theorem ld_exec (d b : Var) (off : Nat) (s : State) (hp : InRegions (s.rd ++ s.wr) (s.r b + BitVec.ofNat 64 off) 8) :
    execBlock isa [.ld d b off] s =
      some (s.set d (s.mem.readW (s.r b + BitVec.ofNat 64 off) 64), [Leak.addr (s.r b + BitVec.ofNat 64 off)]) := by
  simp only [execBlock, isa, exec, State.load, hp, ite_true, Option.map_some, addrs, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]

/-- The facts a Montgomery round needs and provides (`i`: round index). -/
structure RowPre (offA offB offN offMp i : Nat) (s : State) : Prop where
  z : s.r 12 = 0
  e : s.r (rot i 7) = 0
  pA : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offA + 8 * k)) 8
  pB : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 8
  pN : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8
  pM : InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 offMp) 8

/-- The value of the accumulator of round `i`. -/
def acc (s : State) (i n : Nat) : Nat := lsum (fun k => (s.r (rot i k)).toNat) n

theorem rot_ne_z (i k : Nat) : rot i k ≠ 12 := rot_ne _ _ _ (by simp)
theorem rot_ne_0 (i k : Nat) : rot i k ≠ 0 := rot_ne _ _ _ (by simp)
theorem rot_ne_9 (i k : Nat) : rot i k ≠ 9 := rot_ne _ _ _ (by simp)
theorem rot_ne_10 (i k : Nat) : rot i k ≠ 10 := rot_ne _ _ _ (by simp)
theorem rot_ne_11 (i k : Nat) : rot i k ≠ 11 := rot_ne _ _ _ (by simp)
theorem rot_ne_13 (i k : Nat) : rot i k ≠ 13 := rot_ne _ _ _ (by simp)
theorem rot_ne_14 (i k : Nat) : rot i k ≠ 14 := rot_ne _ _ _ (by simp)
theorem rot_ne_rot (i j k : Nat) (hj : j < 8) (hk : k < 8) (h : j ≠ k) : rot i j ≠ rot i k :=
  fun e => h (rot_inj i j k hj hk e)

set_option exponentiation.threshold 1000 in
theorem montRow_ok (offA offB offN offMp i : Nat) (s : State) (h : RowPre offA offB offN offMp i s) :
    WP isa (.block (montRow offA offB offN offMp i)) s (fun q =>
      acc q i 8 = acc s i 7 + lsum (rowX s 14 (fun j => offA + 8 * j)) 6 *
          (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat +
        Mont.qDigit (s.mem.readW (s.r 13 + BitVec.ofNat 64 offMp) 64).toNat
          (acc s i 7 + lsum (rowX s 14 (fun j => offA + 8 * j)) 6 *
            (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat) *
          lsum (rowX s 13 (fun j => offN + 8 * j)) 6 ∧
      q.r 12 = 0 ∧ q.r 13 = s.r 13 ∧ q.r 14 = s.r 14 ∧
      q.mem = s.mem ∧ q.rd = s.rd ∧ q.wr = s.wr ∧ q.labels = s.labels) := by
  unfold montRow
  apply WP.block_append; apply WP.block_append; apply WP.block_append; apply WP.block_append
  apply WP.block_append
  -- load b_i
  refine WP.block_intro _ (ld_exec 0 14 _ s h.pB) ?_
  set s1 := s.set 0 (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64) with hs1
  have s1r : ∀ v, v ≠ 0 → s1.r v = s.r v := fun v hv => by rw [hs1, State.set_r, Function.update_of_ne hv]
  have s1mem : s1.mem = s.mem := by rw [hs1]; rfl
  have s1rd : s1.rd = s.rd := by rw [hs1]; rfl
  have s1wr : s1.wr = s.wr := by rw [hs1]; rfl
  have s1lab : s1.labels = s.labels := by rw [hs1]; rfl
  -- multiply row
  refine WP.mono (macRow_ok (rot i) 14 (fun j => offA + 8 * j) 10 11 9 12 6 (rowRegs i 14 (by simp)) s1
    (by rw [s1r _ (by decide)]; exact h.z)
    (fun k hk => by rw [s1r _ (by decide)]; exact h.pA k hk)) ?_
  intro s2 h2
  have s2r : ∀ v, (∀ k < 6, v ≠ rot i k) → v ≠ 10 → v ≠ 11 → v ≠ 9 → s2.r v = s1.r v := h2.frame
  have hz2 : s2.r 12 = 0 := by
    rw [s2r _ (fun k _ => (rot_ne_z i k).symm) (by decide) (by decide) (by decide), s1r _ (by decide)]; exact h.z
  have he2 : s2.r (rot i 7) = 0 := by
    rw [s2r _ (fun k hk => rot_ne_rot i 7 k (by omega) (by omega) (by omega)) (rot_ne_10 _ _) (rot_ne_11 _ _)
      (rot_ne_9 _ _), s1r _ (rot_ne_0 _ _)]; exact h.e
  -- top of the product
  obtain ⟨q3, hq3, v3, f3, m3, rd3, wr3, l3⟩ := addTop_exec (rot i 6) 11 (rot i 7) 12 s2 (rot_ne_11 _ _)
    (rot_ne_rot i 6 7 (by omega) (by omega) (by omega)) (rot_ne_z _ _) (rot_ne_11 _ _) (rot_ne_z _ _) hz2
    (by rw [he2]; decide)
  refine WP.block_intro q3 hq3 ?_
  set s3 := q3.1 with hs3
  have hz3 : s3.r 12 = 0 := by rw [f3 _ (rot_ne_z _ _).symm (rot_ne_z _ _).symm]; exact hz2
  -- quotient digit
  have r13 : s3.r 13 = s.r 13 := by
    rw [f3 _ (rot_ne_13 _ _).symm (rot_ne_13 _ _).symm,
      s2r _ (fun k _ => (rot_ne_13 i k).symm) (by decide) (by decide) (by decide), s1r _ (by decide)]
  have mem3 : s3.mem = s.mem := by rw [m3, h2.mem, s1mem]
  have rd3' : s3.rd = s.rd := by rw [rd3, h2.rd, s1rd]
  have wr3' : s3.wr = s.wr := by rw [wr3, h2.wr, s1wr]
  obtain ⟨q4, hq4, v4, f4, m4, rd4, wr4, l4⟩ := qCompute_exec (rot i 0) 13 offMp 10 11 9 s3 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r13, rd3', wr3']; exact h.pM)
  refine WP.block_intro q4 hq4 ?_
  set s4 := q4.1 with hs4
  have s4r : ∀ v, v ≠ 0 → v ≠ 10 → v ≠ 11 → v ≠ 9 → s4.r v = s3.r v := f4
  -- reduction row
  refine WP.mono (macRow_ok (rot i) 13 (fun j => offN + 8 * j) 10 11 9 12 6 (rowRegs i 13 (by simp)) s4
    (by rw [s4r _ (by decide) (by decide) (by decide) (by decide)]; exact hz3)
    (fun k hk => by
      rw [s4r _ (by decide) (by decide) (by decide) (by decide), r13, rd4, wr4, rd3', wr3']; exact h.pN k hk)) ?_
  intro s5 h5
  have s5r : ∀ v, (∀ k < 6, v ≠ rot i k) → v ≠ 10 → v ≠ 11 → v ≠ 9 → s5.r v = s4.r v := h5.frame
  have hz5 : s5.r 12 = 0 := by
    rw [s5r _ (fun k _ => (rot_ne_z i k).symm) (by decide) (by decide) (by decide),
      s4r _ (by decide) (by decide) (by decide) (by decide)]; exact hz3
  -- the untouched limbs through the reduction row
  have s5t : ∀ k, 6 ≤ k → k < 8 → s5.r (rot i k) = s3.r (rot i k) := fun k hk1 hk2 => by
    rw [s5r _ (fun j hj => rot_ne_rot i k j (by omega) (by omega) (by omega)) (rot_ne_10 _ _) (rot_ne_11 _ _)
      (rot_ne_9 _ _), s4r _ (rot_ne_0 _ _) (rot_ne_10 _ _) (rot_ne_11 _ _) (rot_ne_9 _ _)]
  have s4t : ∀ k, s4.r (rot i k) = s3.r (rot i k) := fun k => s4r _ (rot_ne_0 _ _) (rot_ne_10 _ _)
    (rot_ne_11 _ _) (rot_ne_9 _ _)
  have e3 : (s3.r (rot i 7)).toNat ≤ 1 := by
    have := (s2.r (rot i 6)).isLt; have := (s2.r 11).isLt
    rw [he2] at v3; simp only [toNat_zero64, mul_zero, add_zero] at v3; omega
  obtain ⟨q6, hq6, v6, f6, m6, rd6, wr6, l6⟩ := addTop_exec (rot i 6) 11 (rot i 7) 12 s5 (rot_ne_11 _ _)
    (rot_ne_rot i 6 7 (by omega) (by omega) (by omega)) (rot_ne_z _ _) (rot_ne_11 _ _) (rot_ne_z _ _) hz5
    (by rw [s5t 7 (by omega) (by omega)]; omega)
  refine WP.block_intro q6 hq6 ?_
  set s6 := q6.1 with hs6
  have mem5 : s5.mem = s.mem := by rw [h5.mem, m4, mem3]
  refine ⟨?_, ?_, ?_, ?_, by rw [m6, mem5], by rw [rd6, h5.rd, rd4, rd3'], by rw [wr6, h5.wr, wr4, wr3'],
    by rw [l6, h5.labels, l4, l3, h2.labels, s1lab]⟩
  · -- the arithmetic
    have hv2 := h2.val
    have hv5 := h5.val
    rw [cin6] at hv2 hv5
    -- limbs 0..5 before each row
    have l1 : lsum (fun k => (s1.r (rot i k)).toNat) 6 = lsum (fun k => (s.r (rot i k)).toNat) 6 :=
      lsum_congr _ _ _ (fun k _ => by rw [s1r _ (rot_ne_0 _ _)])
    have l3' : lsum (fun k => (s3.r (rot i k)).toNat) 6 = lsum (fun k => (s2.r (rot i k)).toNat) 6 :=
      lsum_congr _ _ _ (fun k hk => by
        rw [f3 _ (rot_ne_rot i k 6 (by omega) (by omega) (by omega))
          (rot_ne_rot i k 7 (by omega) (by omega) (by omega))])
    have l4 : lsum (fun k => (s4.r (rot i k)).toNat) 6 = lsum (fun k => (s3.r (rot i k)).toNat) 6 :=
      lsum_congr _ _ _ (fun k _ => by rw [s4t])
    have l6' : lsum (fun k => (s6.r (rot i k)).toNat) 6 = lsum (fun k => (s5.r (rot i k)).toNat) 6 :=
      lsum_congr _ _ _ (fun k hk => by
        rw [f6 _ (rot_ne_rot i k 6 (by omega) (by omega) (by omega))
          (rot_ne_rot i k 7 (by omega) (by omega) (by omega))])
    have rX1 : rowX s1 14 (fun j => offA + 8 * j) = rowX s 14 (fun j => offA + 8 * j) := by
      funext k; simp only [rowX, s1mem, s1r 14 (by decide)]
    have rX4 : rowX s4 13 (fun j => offN + 8 * j) = rowX s 13 (fun j => offN + 8 * j) := by
      funext k; simp only [rowX, m4, mem3, s4r 13 (by decide) (by decide) (by decide) (by decide), r13]
    have hb : (s1.r 0).toNat = (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat := by
      rw [hs1, State.set_r, Function.update_self]
    have s2t6 : s2.r (rot i 6) = s.r (rot i 6) := by
      rw [s2r _ (fun k hk => rot_ne_rot i 6 k (by omega) (by omega) (by omega)) (rot_ne_10 _ _) (rot_ne_11 _ _)
        (rot_ne_9 _ _), s1r _ (rot_ne_0 _ _)]
    have U3 : acc s3 i 7 + 2 ^ (64 * 7) * (s3.r (rot i 7)).toNat =
        acc s i 7 + lsum (rowX s 14 (fun j => offA + 8 * j)) 6 *
          (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat := by
      unfold acc
      rw [lsum_succ, lsum_succ _ 6, l3']
      rw [he2, s2t6] at v3
      rw [l1, rX1, hb] at hv2
      simp only [toNat_zero64, mul_zero, add_zero] at v3
      zify at v3 hv2 ⊢
      linear_combination hv2 + (2 : ℤ) ^ (64 * 6) * v3
    -- the quotient digit
    have hq : (s4.r 0).toNat = Mont.qDigit (s.mem.readW (s.r 13 + BitVec.ofNat 64 offMp) 64).toNat
        (acc s i 7 + lsum (rowX s 14 (fun j => offA + 8 * j)) 6 *
          (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat) := by
      rw [v4, r13, mem3]
      unfold Mont.qDigit
      rw [← U3, acc, lsum_mod _ 6 _ (s3.r (rot i 0)).isLt]
    have U6 : acc s6 i 8 = acc s3 i 7 + 2 ^ (64 * 7) * (s3.r (rot i 7)).toNat + (s4.r 0).toNat *
        lsum (rowX s 13 (fun j => offN + 8 * j)) 6 := by
      unfold acc
      rw [lsum_succ, lsum_succ _ 6, lsum_succ _ 6, l6']
      rw [s5t 6 (by omega) (by omega), s5t 7 (by omega) (by omega)] at v6
      rw [l4, rX4] at hv5
      zify at v6 hv5 ⊢
      linear_combination hv5 + (2 : ℤ) ^ (64 * 6) * v6
    rw [U6, U3, hq]
  · rw [f6 _ (rot_ne_z _ _).symm (rot_ne_z _ _).symm]; exact hz5
  · rw [f6 _ (rot_ne_13 _ _).symm (rot_ne_13 _ _).symm,
      s5r _ (fun k _ => (rot_ne_13 i k).symm) (by decide) (by decide) (by decide),
      s4r _ (by decide) (by decide) (by decide) (by decide), r13]
  · rw [f6 _ (rot_ne_14 _ _).symm (rot_ne_14 _ _).symm,
      s5r _ (fun k _ => (rot_ne_14 i k).symm) (by decide) (by decide) (by decide),
      s4r _ (by decide) (by decide) (by decide) (by decide),
      f3 _ (rot_ne_14 _ _).symm (rot_ne_14 _ _).symm,
      s2r _ (fun k _ => (rot_ne_14 i k).symm) (by decide) (by decide) (by decide), s1r _ (by decide)]

end CC.Limb
