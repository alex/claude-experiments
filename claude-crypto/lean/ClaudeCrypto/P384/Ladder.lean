import ClaudeCrypto.P384.Scalar
import ClaudeCrypto.Limb.Sym

/-!
# The double-scalar multiplication `u₁·G + u₂·Q`
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

theorem movOr_exec (s : State) :
    ∃ q, execBlock isa [.mov 12 10, .or 12 11] s = some q ∧ q.1.r 12 = s.r 10 ||| s.r 11 ∧
      RegsExcept [12] s q.1 ∧ q.1.cf = none ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  have h1 : (11 : Var) ≠ 12 := by decide
  limb_sym [h1]
  refine ⟨_, rfl, by simp, fun v hv => ?_, rfl, rfl, rfl, rfl, rfl⟩
  have : v ≠ 12 := by simpa using hv
  simp [Function.update_of_ne this]

theorem bits_or_ne_zero (b₁ b₂ : ℕ) (h₁ : b₁ < 2) (h₂ : b₂ < 2) :
    (BitVec.ofNat 64 b₁ ||| BitVec.ofNat 64 b₂ != 0) = decide (b₁ = 1 ∨ b₂ = 1) := by
  interval_cases b₁ <;> interval_cases b₂ <;> rfl

theorem ladder_math (A B b₁ b₂ : ℕ) (G Q : Point) :
    2 • (A • G + B • Q) + (b₁ • G + b₂ • Q) = (2 * A + b₁) • G + (2 * B + b₂) • Q := by
  rw [add_nsmul, add_nsmul, nsmul_add, smul_smul, smul_smul]; abel

/-- Choose the operand from the table by the two bits. -/
theorem select_ok (q : State) (h : Inv q) (G Q : Point) (hG : PtAt q sG G) (hQ : PtAt q sQ Q)
    (hGQ : PtAt q sGQ (G + Q)) (b₁ b₂ : ℕ) (h₁ : b₁ < 2) (h₂ : b₂ < 2) (hcf : q.cf = none)
    (h10 : q.r 10 = BitVec.ofNat 64 b₁) (h11 : q.r 11 = BitVec.ofNat 64 b₂) :
    WP isa (.ite (.nez 10) (.ite (.nez 11) (.block (copy3 3 sGQ)) (.block (copy3 3 sG)))
                           (.ite (.nez 11) (.block (copy3 3 sQ)) (.block []))) q
      (fun q' => Inv q' ∧ Eff [3, 4, 5] q q' ∧ q'.r 12 = q.r 12 ∧ q'.cf = none ∧
        (b₁ = 1 ∨ b₂ = 1 → PtAt q' 3 (b₁ • G + b₂ • Q))) := by
  have cp : ∀ a P, a + 3 ≤ nSlots → 6 ≤ a → PtAt q a P → WP isa (.block (copy3 3 a)) q
      (fun q' => Inv q' ∧ Eff [3, 4, 5] q q' ∧ q'.r 12 = q.r 12 ∧ q'.cf = none ∧ PtAt q' 3 P) := by
    intro a P ha ha6 hP
    apply block_wp (copy3_exec 3 a q h (by decide) ha (by omega))
    rintro q' ⟨E, v, r, c⟩
    exact ⟨h.frm E.frm, E, r 12 (by decide), by rw [c, hcf], hP.congr v⟩
  apply WP.ite _ (bit_cond h₁ hcf h10)
  · intro hb; have e1 : b₁ = 1 := by simpa using hb
    apply WP.ite _ (bit_cond h₂ hcf h11)
    · intro hb'; have e2 : b₂ = 1 := by simpa using hb'
      refine WP.mono (cp sGQ _ (by decide) (by decide) hGQ) ?_
      rintro q' ⟨a, b, c, d, e⟩
      exact ⟨a, b, c, d, fun _ => by rw [e1, e2, one_nsmul, one_nsmul]; exact e⟩
    · intro hb'; have e2 : b₂ = 0 := by simp at hb'; omega
      refine WP.mono (cp sG _ (by decide) (by decide) hG) ?_
      rintro q' ⟨a, b, c, d, e⟩
      exact ⟨a, b, c, d, fun _ => by rw [e1, e2, one_nsmul, zero_nsmul, add_zero]; exact e⟩
  · intro hb; have e1 : b₁ = 0 := by simp at hb; omega
    apply WP.ite _ (bit_cond h₂ hcf h11)
    · intro hb'; have e2 : b₂ = 1 := by simpa using hb'
      refine WP.mono (cp sQ _ (by decide) (by decide) hQ) ?_
      rintro q' ⟨a, b, c, d, e⟩
      exact ⟨a, b, c, d, fun _ => by rw [e1, e2, one_nsmul, zero_nsmul, zero_add]; exact e⟩
    · intro hb'; have e2 : b₂ = 0 := by simp at hb'; omega
      apply WP.block_nil
      exact ⟨h, (Eff.refl q).mono (by simp), rfl, hcf, fun h' => by omega⟩

/-- Slots written by the ladder. -/
def ladW : List Nat := ptW ++ [sU1, sU2]

/-- The ladder invariant with `m` iterations left. -/
def LadInv (s0 : State) (G Q : Point) (u₁ u₂ m : ℕ) (s : State) : Prop :=
  0 < m ∧ m ≤ 384 ∧ Inv s ∧ Keep ladW s0 s ∧ cnt s = BitVec.ofNat 64 m ∧
    sv s sU1 = u₁ * 2 ^ (384 - m) % 2 ^ 384 ∧ sv s sU2 = u₂ * 2 ^ (384 - m) % 2 ^ 384 ∧
    PtAt s 0 ((u₁ / 2 ^ m) • G + (u₂ / 2 ^ m) • Q)

theorem table_keep {s0 s : State} {a : ℕ} {P : Point} (hK : Keep ladW s0 s) (h : PtAt s0 a P)
    (ha : 15 ≤ a) (ha' : a + 3 ≤ sU1) : PtAt s a P :=
  h.congr fun k hk => hK.2 _ (by unfold sU1 nSlots at *; omega) (by
    simp only [ladW, List.mem_append, mem_ptW, List.mem_cons, List.not_mem_nil, or_false, sU1, sU2] at ha' ⊢
    omega)

theorem ladder_ok (s0 : State) (G Q : Point) (u₁ u₂ : ℕ) (hG : PtAt s0 sG G) (hQ : PtAt s0 sQ Q)
    (hGQ : PtAt s0 sGQ (G + Q)) :
    ∀ m s, LadInv s0 G Q u₁ u₂ m s → WP isa ladder s (fun q => Inv q ∧ Keep ladW s0 q ∧
      PtAt q 0 (u₁ • G + u₂ • Q)) := by
  intro m s hs
  unfold ladder
  refine WP.loop (M := isa) (LadInv s0 G Q u₁ u₂) ?_ m s hs
  clear hs s m
  intro m s ⟨hm0, hm, hI, hK, hc, hx1, hx2, hP⟩
  obtain ⟨c1, d1, e1⟩ := bit_step u₁ (384 - m) (by omega)
  obtain ⟨c2, d2, e2⟩ := bit_step u₂ (384 - m) (by omega)
  simp only [show 383 - (384 - m) = m - 1 by omega, show 384 - (384 - m) = m by omega] at c1 d1 c2 d2
  simp only [show 384 - m + 1 = 384 - (m - 1) by omega] at e1 e2
  set b₁ := u₁ / 2 ^ (m - 1) % 2
  set b₂ := u₂ / 2 ^ (m - 1) % 2
  have hb₁ : b₁ < 2 := Nat.mod_lt _ (by decide)
  have hb₂ : b₂ < 2 := Nat.mod_lt _ (by decide)
  -- double
  apply WP.seq
  refine WP.mono (dbl_ok s hI _ hP) ?_
  rintro q1 ⟨hI1, hE1, hP1⟩
  -- bits
  apply WP.seq
  obtain ⟨qa, hqa, hEa, hxa, hba, hra, -⟩ :=
    topBit_exec sU1 10 q1 hI1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hIa := hI1.frm hEa.frm
  obtain ⟨qb, hqb, hEb, hxb, hbb, hrb, -⟩ :=
    topBit_exec sU2 11 qa.1 hIa (by decide) (by decide) (by decide) (by decide) (by decide)
  have hIb := hIa.frm hEb.frm
  obtain ⟨qc, hqc, h12, hrc, hcfc, hmc, hrdc, hwrc, hlc⟩ := movOr_exec qb.1
  obtain ⟨qab, hqab, eab⟩ := exec_app hqa hqb
  obtain ⟨q2, hq2, e2'⟩ := exec_app hqab (by rw [eab]; exact hqc)
  refine WP.block_intro q2 hq2 ?_
  have hEc : Eff [] qb.1 qc.1 := eff_of_mem (hrc 13 (by decide)) (hrc 14 (by decide)) hmc hrdc hwrc hlc
  have hE2 : Eff [sU1, sU2] q1 q2.1 := by rw [e2']; exact ((hEa.trans hEb).trans hEc).mono (by simp)
  have hI2 : Inv q2.1 := hI1.frm hE2.frm
  have hsU1 : sv q1 sU1 = sv s sU1 := hE1.keep sU1 (by decide) (by decide)
  have hsU2 : sv q1 sU2 = sv s sU2 := hE1.keep sU2 (by decide) (by decide)
  have r10 : q2.1.r 10 = BitVec.ofNat 64 b₁ := by
    rw [e2', hrc 10 (by decide), hrb 10 (by decide), hba, hsU1, hx1, c1]
  have r11 : q2.1.r 11 = BitVec.ofNat 64 b₂ := by
    rw [e2', hrc 11 (by decide), hbb, hEa.keep sU2 (by decide) (by decide), hsU2, hx2, c2]
  have r12 : q2.1.r 12 = BitVec.ofNat 64 b₁ ||| BitVec.ofNat 64 b₂ := by
    rw [e2', h12, hrb 10 (by decide), hba, hbb, hEa.keep sU2 (by decide) (by decide), hsU1, hsU2, hx1, hx2, c1, c2]
  have hcf2 : q2.1.cf = none := by rw [e2']; exact hcfc
  have hx1' : sv q2.1 sU1 = u₁ * 2 ^ (384 - (m - 1)) % 2 ^ 384 := by
    rw [e2', hEc.keep sU1 (by decide) (by simp), hEb.keep sU1 (by decide) (by decide), hxa, hsU1, hx1, e1]
  have hx2' : sv q2.1 sU2 = u₂ * 2 ^ (384 - (m - 1)) % 2 ^ 384 := by
    rw [e2', hEc.keep sU2 (by decide) (by simp), hxb, hEa.keep sU2 (by decide) (by decide), hsU2, hx2, e2]
  have hK2 : Keep ladW s0 q2.1 := (hK.trans (hE1.keep'.trans hE2.keep')).mono
    (by intro i hi; simp only [ladW, ptW, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false, sU1, sU2] at hi ⊢; omega)
  have hP2 : PtAt q2.1 0 (2 • ((u₁ / 2 ^ m) • G + (u₂ / 2 ^ m) • Q)) := hP1.of_eff hE2 (by decide) (by decide)
  -- select
  apply WP.seq
  refine WP.mono (select_ok q2.1 hI2 G Q (table_keep hK2 hG (by decide) (by decide))
    (table_keep hK2 hQ (by decide) (by decide)) (table_keep hK2 hGQ (by decide) (by decide))
    b₁ b₂ hb₁ hb₂ hcf2 r10 r11) ?_
  rintro q3 ⟨hI3, hE3, h123, hcf3, hop⟩
  have hP3 := hP2.of_eff hE3 (by decide) (by decide)
  -- add
  apply WP.seq
  have hadd : WP isa (.ite (.nez 12) addCode (.block [])) q3 (fun q4 => Inv q4 ∧ Eff ptW q3 q4 ∧
      PtAt q4 0 ((u₁ / 2 ^ (m - 1)) • G + (u₂ / 2 ^ (m - 1)) • Q)) := by
    have hcond : isa.eval (.nez 12) q3 = some (decide (b₁ = 1 ∨ b₂ = 1)) := by
      simp only [isa, eval, hcf3, h123, r12, bits_or_ne_zero b₁ b₂ hb₁ hb₂]
    rw [d1, d2, ← ladder_math]
    apply WP.ite _ hcond
    · intro hb
      exact addCode_ok q3 hI3 _ _ hP3 (hop (by simpa using hb))
    · intro hb
      have z1 : b₁ = 0 := by simp at hb; omega
      have z2 : b₂ = 0 := by simp at hb; omega
      apply WP.block_nil
      refine ⟨hI3, (Eff.refl _).mono (by simp), ?_⟩
      rw [z1, z2, zero_nsmul, zero_nsmul, add_zero, add_zero]; exact hP3
  refine WP.mono hadd ?_
  rintro q4 ⟨hI4, hE4, hP4⟩
  -- counter
  obtain ⟨q5, hq5, hF5, hs5, hc5, h95, -, hcf5⟩ := cntDec_exec q4 hI4
  refine WP.block_intro q5 hq5 ?_
  have hc4 : cnt q4 = BitVec.ofNat 64 m := hE4.cnt.trans (hE3.cnt.trans (hE2.cnt.trans (hE1.cnt.trans hc)))
  rw [hc4, ofNat_pred m hm0 (by omega)] at hc5 h95
  have hK5 : Keep ladW s0 q5.1 :=
    (hK2.trans ((hE3.keep'.trans hE4.keep').trans (⟨hF5, fun i hi _ => hs5 i hi⟩ : Keep [] q4 q5.1))).mono
    (by intro i hi; simp only [ladW, ptW, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false, sU1, sU2] at hi ⊢; omega)
  have hI5 := hI4.frm hF5
  have hP5 : PtAt q5.1 0 ((u₁ / 2 ^ (m - 1)) • G + (u₂ / 2 ^ (m - 1)) • Q) :=
    hP4.congr fun k hk => hs5 _ (by unfold nSlots; omega)
  have hx1'' : sv q5.1 sU1 = u₁ * 2 ^ (384 - (m - 1)) % 2 ^ 384 := by
    rw [hs5 _ (by decide), hE4.keep sU1 (by decide) (by decide), hE3.keep sU1 (by decide) (by decide), hx1']
  have hx2'' : sv q5.1 sU2 = u₂ * 2 ^ (384 - (m - 1)) % 2 ^ 384 := by
    rw [hs5 _ (by decide), hE4.keep sU2 (by decide) (by decide), hE3.keep sU2 (by decide) (by decide), hx2']
  by_cases hm1 : m - 1 = 0
  · left
    refine ⟨by rw [cnt_cond hcf5 h95 (by omega)]; simp [hm1], hI5, hK5, ?_⟩
    rw [hm1, pow_zero, Nat.div_one, Nat.div_one] at hP5; exact hP5
  · right
    refine ⟨by rw [cnt_cond hcf5 h95 (by omega)]; simp [hm1], m - 1, by omega,
      by omega, by omega, hI5, hK5, hc5, hx1'', hx2'', hP5⟩

end CC.P384
