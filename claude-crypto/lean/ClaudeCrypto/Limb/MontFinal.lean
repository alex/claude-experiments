import ClaudeCrypto.Limb.MontMul
import ClaudeCrypto.Common.MemLemmas

/-! # Montgomery multiplication: the final conditional subtraction -/

namespace CC.Limb

theorem addr_add_ofNat' (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

/-- Two slots at offsets `x`, `y` from the same base are disjoint. -/
theorem sep_offsets (b : Addr) (x y k l : Nat) (h : x + k ≤ y ∨ y + l ≤ x) (hx : x + k < 2 ^ 64)
    (hy : y + l < 2 ^ 64) (hk : 0 < k) (hl : 0 < l) :
    Mem.Sep (b + BitVec.ofNat 64 x) k (b + BitVec.ofNat 64 y) l := by
  rw [sep_add_add]
  unfold Mem.Sep
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx' : x % 2 ^ 64 = x := Nat.mod_eq_of_lt (by omega)
  have hy' : y % 2 ^ 64 = y := Nat.mod_eq_of_lt (by omega)
  rw [hx', hy']
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ 64 - x = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, 2 ^ 64 - y = v := ⟨_, rfl⟩
  have hu' : u + x = 2 ^ 64 := by omega
  have hv' : v + y = 2 ^ 64 := by omega
  rw [hu, hv]
  rcases h with h | h <;> constructor
  · rw [show u + y = (y - x) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show v + x = (x - y) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

/-- Limb `k` of the 6-limb number at `a`. -/
def mlimb (m : Mem) (a : Addr) (k : Nat) : Nat := (m.readW (a + BitVec.ofNat 64 (8 * k)) 64).toNat

/-- One step of `d := t - N` (stored at `fp + offD`). -/
def subStep (offN offD : Nat) (k : Nat) : List Instr :=
  [ .ld 10 13 (offN + 8 * k), .mov 9 (rot 6 k), if k = 0 then .sub 9 10 else .sbb 9 10,
    .st 14 (offD + 8 * k) 9 ]

def subChain (offN offD : Nat) : List Instr := ((List.range 6).map fun k => subStep offN offD (0 + k)).flatten

section
variable (offN offD : Nat) (s0 : State)

def dAddr : Addr := s0.r 14 + BitVec.ofNat 64 offD
def nAddr : Addr := s0.r 13 + BitVec.ofNat 64 offN

/-- After `j` steps: `d[0..j) + N[0..j) = t[0..j) + 2^(64 j) · borrow`. -/
structure SubInv (j : Nat) (s : State) : Prop where
  regs : ∀ v, v ≠ 9 → v ≠ 10 → s.r v = s0.r v
  borrow : 0 < j → ∃ b, s.cf = some b ∧ s.sub = true ∧
    lsum (mlimb s.mem (dAddr offD s0)) j + lsum (mlimb s0.mem (nAddr offN s0)) j =
      lsum (fun k => (s0.r (rot 6 k)).toNat) j + 2 ^ (64 * j) * b.toNat
  agree : Mem.Agree s0.mem s.mem ⟨dAddr offD s0, 48⟩
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
end

theorem borrow_eq (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (borrowOut a b c).toNat := by
  have ha := a.isLt; have hb := b.isLt
  simp only [borrowOut, blt_toNat, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_mod, Nat.reducePow, Nat.one_mod,
    Nat.add_zero] <;> generalize a.toNat = x at * <;> generalize b.toNat = y at * <;> split_ifs <;> omega

theorem subStep_ok (offN offD : Nat) (s0 : State) (hoffD : offD + 48 < 2 ^ 63) (hoffN : offN + 48 < 2 ^ 63)
    (pN : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pD : ∀ k < 6, InRegions s0.wr (s0.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8)
    (hsep : ∀ k < 6, Mem.Sep (dAddr offD s0) 48 (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (k : Nat) (hk : k < 6) (s : State) (h : SubInv offN offD s0 k s) :
    ∃ q, execBlock isa (subStep offN offD k) s = some q ∧ SubInv offN offD s0 (k + 1) q.1 := by
  have r13 : s.r 13 = s0.r 13 := h.regs 13 (by decide) (by decide)
  have r14 : s.r 14 = s0.r 14 := h.regs 14 (by decide) (by decide)
  have rt : s.r (rot 6 k) = s0.r (rot 6 k) := h.regs _ (rot_ne_9 _ _) (rot_ne_10 _ _)
  have hpN : InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8 := by
    rw [h.rd, h.wr, r13]; exact pN k hk
  have hpD : InRegions s.wr (s.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8 := by rw [h.wr, r14]; exact pD k hk
  have hNk : s.mem.readW (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 64 =
      s0.mem.readW (nAddr offN s0 + BitVec.ofNat 64 (8 * k)) 64 := by
    rw [r13, h.agree.readW _ _ (hsep k hk), nAddr, addr_add_ofNat']
  -- the incoming borrow
  obtain ⟨b, hb, hsubb, hval⟩ : ∃ b : Bool, (k = 0 → b = false) ∧ (0 < k → s.cf = some b ∧ s.sub = true) ∧
      lsum (mlimb s.mem (dAddr offD s0)) k + lsum (mlimb s0.mem (nAddr offN s0)) k =
        lsum (fun j => (s0.r (rot 6 j)).toNat) k + 2 ^ (64 * k) * b.toNat := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; exact ⟨false, fun _ => rfl, fun h => absurd h (by omega), by simp [lsum]⟩
    · obtain ⟨b, h1, h2, h3⟩ := h.borrow hk0
      exact ⟨b, fun h => absurd h (by omega), fun _ => ⟨h1, h2⟩, h3⟩
  -- execute
  set N := s.mem.readW (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 64 with hN
  set t := s.r (rot 6 k) with ht
  have hexec : ∃ q, execBlock isa (subStep offN offD k) s = some q ∧
      q.1.r = Function.update (Function.update s.r 10 N) 9 (t - N - (BitVec.ofBool b).setWidth 64) ∧
      q.1.cf = some (borrowOut t N b) ∧ q.1.sub = true ∧
      q.1.mem = s.mem.writeW (s.r 14 + BitVec.ofNat 64 (offD + 8 * k)) (t - N - (BitVec.ofBool b).setWidth 64) ∧
      q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
    have n9 : rot 6 k ≠ 10 := rot_ne_10 _ _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hb0 := hb hk0
      subst hk0 hb0
      simp only [subStep, ite_true]
      limb_sym [hpN, hpD, n9]
      refine ⟨_, rfl, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
      · simp [ht, hN]
      · simp [ht, hN]
      · simp [ht, hN]
    · obtain ⟨hcf, hsub⟩ := hsubb hk0
      simp only [subStep, show k ≠ 0 by omega, ite_false]
      limb_sym [hpN, hpD, n9, hcf, hsub]
      refine ⟨_, rfl, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
      · simp [ht, hN]
      · simp [ht, hN]
      · simp [ht, hN]
  obtain ⟨q, hq, qr, qcf, qsub, qm, qrd, qwr, ql⟩ := hexec
  refine ⟨q, hq, ?_⟩
  have hDk : s.r 14 + BitVec.ofNat 64 (offD + 8 * k) = dAddr offD s0 + BitVec.ofNat 64 (8 * k) := by
    rw [r14, dAddr, addr_add_ofNat']
  refine ⟨fun v h9 h10 => ?_, fun _ => ⟨_, qcf, qsub, ?_⟩, ?_, qrd.trans h.rd, qwr.trans h.wr, ql.trans h.labels⟩
  · rw [qr, Function.update_of_ne h9, Function.update_of_ne h10]; exact h.regs v h9 h10
  · -- the arithmetic
    have hm : ∀ j < k, mlimb q.1.mem (dAddr offD s0) j = mlimb s.mem (dAddr offD s0) j := by
      intro j hj
      unfold mlimb
      rw [qm, hDk, dAddr, addr_add_ofNat', addr_add_ofNat', Mem.readW_writeW_sep]
      exact sep_offsets _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    have hmk : mlimb q.1.mem (dAddr offD s0) k = (t - N - (BitVec.ofBool b).setWidth 64).toNat := by
      unfold mlimb; rw [qm, hDk, Mem.readW_writeW_same_64]
    have hNk' : mlimb s0.mem (nAddr offN s0) k = N.toNat := by unfold mlimb; rw [hNk]
    have ht' : (s0.r (rot 6 k)).toNat = t.toNat := by rw [← rt]
    rw [lsum_succ, lsum_succ, lsum_succ, lsum_congr _ _ _ hm, hmk, hNk', ht']
    have be := borrow_eq t N b
    rw [show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
    zify at hval be ⊢
    linear_combination hval + (2 : ℤ) ^ (64 * k) * be
  · rw [qm]
    refine h.agree.writeW _ _ ?_
    rw [hDk]
    exact Region.contains_offset _ _ _ _ (by omega) (by decide)

theorem subChain_ok (offN offD : Nat) (s0 : State) (hoffD : offD + 48 < 2 ^ 63) (hoffN : offN + 48 < 2 ^ 63)
    (pN : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pD : ∀ k < 6, InRegions s0.wr (s0.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8)
    (hsep : ∀ k < 6, Mem.Sep (dAddr offD s0) 48 (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8) :
    WP isa (.block (subChain offN offD)) s0 (SubInv offN offD s0 6) := by
  have := WP.block_iter (M := isa) (subStep offN offD) (SubInv offN offD s0) 0 6
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := subStep_ok offN offD s0 hoffD hoffN pN pD hsep (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') s0
    ⟨fun _ _ _ => rfl, fun h => absurd h (by omega), Mem.Agree.refl _ _, rfl, rfl, rfl⟩
  simpa [subChain] using this

def copyStep (offD : Nat) (k : Nat) : List Instr := [.st 14 (offD + 8 * k) (rot 6 k)]
def copyBack (offD : Nat) : List Instr := ((List.range 6).map fun k => copyStep offD (0 + k)).flatten

structure CopyInv (offD : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  regs : s.r = s0.r
  cf : s.cf = s0.cf
  lim : ∀ k < j, mlimb s.mem (dAddr offD s0) k = (s0.r (rot 6 k)).toNat
  agree : Mem.Agree s0.mem s.mem ⟨dAddr offD s0, 48⟩
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels

theorem copyBack_ok (offD : Nat) (s0 : State) (hoffD : offD + 48 < 2 ^ 63)
    (pD : ∀ k < 6, InRegions s0.wr (s0.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8) :
    WP isa (.block (copyBack offD)) s0 (CopyInv offD s0 6) := by
  have := WP.block_iter (M := isa) (copyStep offD) (CopyInv offD s0) 0 6
    (fun i hi s hs => by
      have hp : InRegions s.wr (s.r 14 + BitVec.ofNat 64 (offD + 8 * (0 + i))) 8 := by
        rw [hs.wr, hs.regs]; exact pD _ (by omega)
      have hDk : s.r 14 + BitVec.ofNat 64 (offD + 8 * (0 + i)) = dAddr offD s0 + BitVec.ofNat 64 (8 * (0 + i)) := by
        rw [hs.regs, dAddr, addr_add_ofNat']
      obtain ⟨q, hq, hqs⟩ : ∃ q, execBlock isa (copyStep offD (0 + i)) s = some q ∧
          q.1 = { s with mem := s.mem.writeW (s.r 14 + BitVec.ofNat 64 (offD + 8 * (0 + i))) (s.r (rot 6 (0 + i))) } :=
        ⟨_, by simp only [copyStep]; limb_sym [hp]; rfl, rfl⟩
      refine WP.block_intro q hq ?_
      rw [hqs]
      refine ⟨hs.regs, hs.cf, fun k hk => ?_, ?_, hs.rd, hs.wr, hs.labels⟩
      · unfold mlimb
        simp only
        rw [hDk]
        rcases Nat.lt_or_ge k (0 + i) with hk' | hk'
        · rw [Mem.readW_writeW_sep _ _ _ _ _ (sep_offsets _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
            (by omega))]
          exact hs.lim k hk'
        · have : k = 0 + i := by omega
          subst this
          rw [Mem.readW_writeW_same_64, hs.regs]
      · simp only
        refine hs.agree.writeW _ _ ?_
        rw [hDk]
        exact Region.contains_offset _ _ _ _ (by omega) (by decide)) s0
    ⟨rfl, rfl, fun k hk => absurd hk (by omega), Mem.Agree.refl _ _, rfl, rfl, rfl⟩
  simpa [copyBack] using this

theorem final_math (D N L T t6 b W : Nat) (hW : 0 < W) (hb : b ≤ 1) (h1 : D + N = L + W * b)
    (h2 : T = L + W * t6) (hT : T < 2 * N) (hN : N < W) (hD : D < W) (hL : L < W) :
    (t6 < b → T < N ∧ T = L) ∧ (¬ t6 < b → ¬ T < N ∧ T - N = D) := by
  constructor
  · intro h
    have : t6 = 0 := by omega
    have : b = 1 := by omega
    subst_vars; constructor <;> nlinarith
  · intro h
    rcases Nat.eq_zero_or_pos t6 with ht | ht
    · have : b = 0 := by omega
      subst_vars; simp at *; try omega
    · -- then T ≥ W > N, impossible as T < 2N forces t6 = b; handle generally
      have hTW : W ≤ T := by rw [h2]; nlinarith
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · subst hb0; simp at h1; nlinarith
      · have : b = 1 := by omega
        subst this
        have : t6 = 1 := by nlinarith
        subst this
        constructor <;> omega

def montTop : List Instr := [.sbb (rot 6 6) 12, .mask 11, .clrc]

def montFinal (offN offD : Nat) : Code Instr Cond :=
  .seq (.block (subChain offN offD ++ montTop)) (.ite (.nez 11) (.block (copyBack offD)) (.block []))

def mval (m : Mem) (a : Addr) (n : Nat) : Nat := lsum (mlimb m a) n

theorem montFinal_ok (offN offD : Nat) (s0 : State) (hoffD : offD + 48 < 2 ^ 63) (hoffN : offN + 48 < 2 ^ 63)
    (pN : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pD : ∀ k < 6, InRegions s0.wr (s0.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8)
    (hsep : ∀ k < 6, Mem.Sep (dAddr offD s0) 48 (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (hz : s0.r 12 = 0) (hT : acc s0 6 7 < 2 * mval s0.mem (nAddr offN s0) 6) :
    WP isa (montFinal offN offD) s0 (fun q =>
      mval q.mem (dAddr offD s0) 6 = (if acc s0 6 7 < mval s0.mem (nAddr offN s0) 6 then acc s0 6 7
        else acc s0 6 7 - mval s0.mem (nAddr offN s0) 6) ∧
      Mem.Agree s0.mem q.mem ⟨dAddr offD s0, 48⟩ ∧ q.r 13 = s0.r 13 ∧ q.r 14 = s0.r 14 ∧ q.rd = s0.rd ∧
      q.wr = s0.wr ∧ q.labels = s0.labels) := by
  unfold montFinal
  apply WP.seq; apply WP.block_append
  refine WP.mono (subChain_ok offN offD s0 hoffD hoffN pN pD hsep) ?_
  intro s1 h1
  obtain ⟨b, hcf, hsub, hval⟩ := h1.borrow (by decide)
  have r66 : s1.r (rot 6 6) = s0.r (rot 6 6) := h1.regs _ (rot_ne_9 _ _) (rot_ne_10 _ _)
  have r12 : s1.r 12 = 0 := (h1.regs 12 (by decide) (by decide)).trans hz
  set B := borrowOut (s1.r (rot 6 6)) (s1.r 12) b with hB
  obtain ⟨q2, hq2, hq2s⟩ : ∃ q, execBlock isa montTop s1 = some q ∧
      q.1 = { (s1.set (rot 6 6) (s1.r (rot 6 6) - s1.r 12 - (BitVec.ofBool b).setWidth 64)).set 11
        (if B then BitVec.allOnes 64 else 0) with cf := none, sub := true } := by
    have n11 : rot 6 6 ≠ 11 := rot_ne_11 _ _
    refine ⟨({ (s1.set (rot 6 6) (s1.r (rot 6 6) - s1.r 12 - (BitVec.ofBool b).setWidth 64)).set 11
        (if B then BitVec.allOnes 64 else 0) with cf := none, sub := true }, []), ?_, rfl⟩
    simp only [montTop]
    limb_sym [hcf, hsub, n11]
    rfl
  refine WP.block_intro q2 hq2 ?_
  set s2 := q2.1 with hs2
  have s2r : ∀ v, v ≠ rot 6 6 → v ≠ 11 → s2.r v = s1.r v := fun v h1 h2 => by
    rw [hq2s]; simp only [State.set_r, Function.update_of_ne h1, Function.update_of_ne h2]
  have s2mem : s2.mem = s1.mem := by rw [hq2s]; rfl
  have s2cf : s2.cf = none := by rw [hq2s]
  have s2m : s2.r 11 = if B then BitVec.allOnes 64 else 0 := by rw [hq2s]; simp [State.set_r]
  -- the arithmetic
  have hN := lsum_lt (mlimb s0.mem (nAddr offN s0)) 6 (fun k _ => BitVec.isLt _)
  have hD := lsum_lt (mlimb s1.mem (dAddr offD s0)) 6 (fun k _ => BitVec.isLt _)
  have hL := lsum_lt (fun k => (s0.r (rot 6 k)).toNat) 6 (fun k _ => BitVec.isLt _)
  have hTe : acc s0 6 7 = lsum (fun k => (s0.r (rot 6 k)).toNat) 6 + 2 ^ (64 * 6) * (s0.r (rot 6 6)).toNat := by
    unfold acc; rw [lsum_succ]; ring
  have hBv : B = decide ((s0.r (rot 6 6)).toNat < b.toNat) := by
    rw [hB, borrowOut, r66, r12, toNat_zero64, Nat.zero_add]
    exact Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])
  have fm := final_math _ _ _ _ _ b.toNat _ (by positivity) (by cases b <;> simp) (by rw [hval]; try ring) hTe
    (by unfold mval at hT; exact hT) hN hD hL
  have regs2 : ∀ v, v ≠ rot 6 6 → v ≠ 11 → v ≠ 9 → v ≠ 10 → s2.r v = s0.r v := fun v a b c d => by
    rw [s2r v a b]; exact h1.regs v c d
  refine WP.ite B (by simp only [isa, eval, s2cf, s2m]; cases B <;> simp) ?_ ?_
  · intro hBt
    have pD' : ∀ k < 6, InRegions s2.wr (s2.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8 := by
      intro k hk
      rw [regs2 14 (rot_ne_14 _ _).symm (by decide) (by decide) (by decide), show s2.wr = s0.wr by
        rw [hq2s]; exact h1.wr]
      exact pD k hk
    refine WP.mono (copyBack_ok offD s2 hoffD pD') ?_
    intro s3 h3
    have hlt : acc s0 6 7 < mval s0.mem (nAddr offN s0) 6 ∧ acc s0 6 7 = lsum (fun k => (s0.r (rot 6 k)).toNat) 6 := by
      rw [hBv] at hBt; exact fm.1 (of_decide_eq_true hBt)
    have hdA : dAddr offD s2 = dAddr offD s0 := by
      unfold dAddr; rw [regs2 14 (rot_ne_14 _ _).symm (by decide) (by decide) (by decide)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (show acc s0 6 7 < mval s0.mem (nAddr offN s0) 6 from hlt.1), hlt.2]
      unfold mval
      apply lsum_congr
      intro k hk
      rw [← hdA, h3.lim k hk, regs2 _ (rot_ne_rot 6 k 6 (by omega) (by omega) (by omega)) (rot_ne_11 _ _)
        (rot_ne_9 _ _) (rot_ne_10 _ _)]
    · have := h3.agree; rw [hdA, s2mem] at this; exact h1.agree.trans this
    · rw [h3.regs]; exact regs2 13 (rot_ne_13 _ _).symm (by decide) (by decide) (by decide)
    · rw [h3.regs]; exact regs2 14 (rot_ne_14 _ _).symm (by decide) (by decide) (by decide)
    · rw [h3.rd, hq2s]; exact h1.rd
    · rw [h3.wr, hq2s]; exact h1.wr
    · rw [h3.labels, hq2s]; exact h1.labels
  · intro hBf
    apply WP.block_nil
    have hge := fm.2 (by rw [hBv] at hBf; simpa using hBf)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (show ¬ acc s0 6 7 < mval s0.mem (nAddr offN s0) 6 from hge.1), s2mem]; exact hge.2.symm
    · rw [s2mem]; exact h1.agree
    · exact regs2 13 (rot_ne_13 _ _).symm (by decide) (by decide) (by decide)
    · exact regs2 14 (rot_ne_14 _ _).symm (by decide) (by decide) (by decide)
    · rw [hq2s]; exact h1.rd
    · rw [hq2s]; exact h1.wr
    · rw [hq2s]; exact h1.labels

end CC.Limb
