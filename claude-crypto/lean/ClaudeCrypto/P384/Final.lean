import ClaudeCrypto.P384.Ladder

/-!
# The point part and the final comparison
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

theorem sv_lt (s : State) (i : Nat) : sv s i < 2 ^ 384 :=
  lsum_lt _ 6 (fun k _ => BitVec.isLt _)

/-! ## `u₁·G + u₂·Q` from the table setup -/

theorem pointPart_ok (s : State) (h : Inv s) (G Q : Point) (hG : PtAt s sG G) (hQ : PtAt s sQ Q) :
    WP isa pointPart s (fun q => Inv q ∧ Keep (ladW ++ [sGQ, sGQ + 1, sGQ + 2]) s q ∧
      PtAt q 0 (sv s sU1 • G + sv s sU2 • Q)) := by
  unfold pointPart
  -- accumulator := G, operand := Q
  apply WP.seq
  obtain ⟨qa, hqa, hEa, hva, -, -⟩ := copy3_exec 0 sG s h (by decide) (by decide) (by decide)
  have hIa := h.frm hEa.frm
  obtain ⟨qb, hqb, hEb, hvb, -, -⟩ := copy3_exec 3 sQ qa.1 hIa (by decide) (by decide) (by decide)
  obtain ⟨q1, hq1, e1⟩ := exec_app hqa hqb
  refine WP.block_intro q1 hq1 ?_
  have hE1 : Eff [0, 1, 2, 3, 4, 5] s q1.1 := by rw [e1]; exact (hEa.trans hEb).mono (by simp)
  have hI1 : Inv q1.1 := h.frm hE1.frm
  have hA1 : PtAt q1.1 0 G := by
    rw [e1]; exact hG.congr fun k hk => by
      rw [hEb.keep _ (by unfold nSlots; omega) (by simp; omega), hva k hk]
  have hB1 : PtAt q1.1 3 Q := by
    rw [e1]; exact hQ.congr fun k hk => by
      rw [hvb k hk, hEa.keep _ (by unfold sQ nSlots; omega) (by simp [sQ]; omega)]
  -- G + Q
  apply WP.seq
  refine WP.mono (addCode_ok q1.1 hI1 G Q hA1 hB1) ?_
  rintro q2 ⟨hI2, hE2, hP2⟩
  -- table entry, zero accumulator, counter
  apply WP.seq
  obtain ⟨qc, hqc, hEc, hvc, -, -⟩ := copy3_exec sGQ 0 q2 hI2 (by decide) (by decide) (by decide)
  have hIc := hI2.frm hEc.frm
  obtain ⟨qd, hqd, hEd, hvd, -⟩ := zeroSlot_exec 0 qc.1 hIc (by decide)
  have hId := hIc.frm hEd.frm
  obtain ⟨qe, hqe, hEe, hve, -⟩ := zeroSlot_exec 1 qd.1 hId (by decide)
  have hIe := hId.frm hEe.frm
  obtain ⟨qf, hqf, hEf, hvf, -⟩ := zeroSlot_exec 2 qe.1 hIe (by decide)
  have hIf := hIe.frm hEf.frm
  obtain ⟨qg, hqg, hFg, hsg, hcg, -⟩ := cntInit_exec 384 qf.1 hIf
  obtain ⟨x1, hx1, f1⟩ := exec_app hqc hqd
  obtain ⟨x2, hx2, f2⟩ := exec_app hx1 (by rw [f1]; exact hqe)
  obtain ⟨x3, hx3, f3⟩ := exec_app hx2 (by rw [f2]; exact hqf)
  obtain ⟨q3, hq3, f4⟩ := exec_app hx3 (by rw [f3]; exact hqg)
  refine WP.block_intro q3 hq3 ?_
  have hK3 : Keep [sGQ, sGQ + 1, sGQ + 2, 0, 1, 2] q2 q3.1 := by
    rw [f4]
    exact ((((hEc.keep'.trans hEd.keep').trans hEe.keep').trans hEf.keep').trans
      (⟨hFg, fun i hi _ => hsg i hi⟩ : Keep [] qf.1 qg.1)).mono (by simp)
  have hI3 : Inv q3.1 := by rw [f4]; exact hIf.frm hFg
  have sv3 : ∀ i < nSlots, i ∉ [0, 1, 2] → sv q3.1 i = sv qc.1 i := fun i hi hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [f4, hsg i hi, hEf.keep i hi (by simpa using hn.2.2), hEe.keep i hi (by simpa using hn.2.1),
      hEd.keep i hi (by simpa using hn.1)]
  have hGQ3 : PtAt q3.1 sGQ (G + Q) := hP2.congr fun k hk => by
    rw [sv3 _ (by unfold sGQ nSlots; omega) (by simp [sGQ]; omega), hvc k hk]
  have hKpre := (hE1.keep'.trans hE2.keep').trans hK3
  have hK13 : Keep (ladW ++ [sGQ, sGQ + 1, sGQ + 2]) s q3.1 :=
    hKpre.mono (by
      intro i hi; simp only [ladW, ptW, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false, sU1, sU2, sGQ] at hi ⊢; omega)
  have tab : ∀ a P, 15 ≤ a → a + 3 ≤ sGQ → PtAt s a P → PtAt q3.1 a P := fun a P h1 h2 hP =>
    hP.congr fun k hk => hK13.2 _ (by unfold sGQ nSlots at *; omega) (by
      simp only [ladW, ptW, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false, sU1, sU2,
        sGQ] at h2 ⊢; omega)
  have hu1 : sv q3.1 sU1 = sv s sU1 := hKpre.2 _ (by decide) (by decide)
  have hu2 : sv q3.1 sU2 = sv s sU2 := hKpre.2 _ (by decide) (by decide)
  -- the ladder
  have hinit : LadInv q3.1 G Q (sv s sU1) (sv s sU2) 384 q3.1 := by
    refine ⟨by decide, le_refl _, hI3, (Keep.refl _).mono (by simp), by rw [f4]; exact hcg, ?_, ?_, ?_⟩
    · rw [hu1, Nat.sub_self, pow_zero, mul_one, Nat.mod_eq_of_lt (sv_lt _ _)]
    · rw [hu2, Nat.sub_self, pow_zero, mul_one, Nat.mod_eq_of_lt (sv_lt _ _)]
    · rw [Nat.div_eq_of_lt (sv_lt _ _), Nat.div_eq_of_lt (sv_lt _ _), zero_nsmul, zero_nsmul, add_zero]
      have z : ∀ k < 3, sv q3.1 k = 0 := fun k hk => by
        rw [f4, hsg k (by unfold nSlots; omega)]
        interval_cases k
        · rw [hEf.keep 0 (by decide) (by decide), hEe.keep 0 (by decide) (by decide), hvd]
        · rw [hEf.keep 1 (by decide) (by decide), hve]
        · exact hvf
      refine ⟨fun k hk => by rw [Nat.zero_add, z k hk]; decide, ?_⟩
      have : dp q3.1 2 = 0 := by unfold dp; rw [z 2 (by decide)]; simp [decode]
      rw [this]; exact jrep_zero _ _
  refine WP.mono (ladder_ok q3.1 G Q (sv s sU1) (sv s sU2) (tab _ _ (by decide) (by decide) hG)
    (tab _ _ (by decide) (by decide) hQ) hGQ3 384 q3.1 hinit) ?_
  rintro q ⟨hI, hK, hP⟩
  exact ⟨hI, (hK13.trans hK).mono (by intro i hi; simp only [List.mem_append] at hi ⊢; tauto), hP⟩

/-! ## The final comparison -/

/-- Steps 6–8 of FIPS 186-5 §6.4.2, given `R₁`. -/
def finalOk (R₁ : Point) (r : ℕ) : Bool :=
  match R₁ with
  | .zero => false
  | .some xR _ _ => xR.val % n == r

theorem finalOk_iff {X Y Z : F} {R₁ : Point} (hR : Jrep X Y Z R₁) (hZ : Z ≠ 0) {r : ℕ} (hr : r < n) :
    finalOk R₁ r = true ↔ (X = (r : F) * Z ^ 2 ∨ (r + n < p ∧ X = ((r + n : ℕ) : F) * Z ^ 2)) := by
  obtain ⟨h', hR'⟩ := (jrep_of_ne hZ).1 hR
  rw [mkPoint_def] at hR'
  rw [← jrep_x_mod_n_eq_iff hR hZ hR' hr, hR']
  simp [finalOk]

theorem ret_ok (v : ℕ) (s : State) (h : Inv s) :
    WP isa (ret v) s (fun q => Inv q ∧ Eff [] s q ∧ q.r 1 = BitVec.ofNat 64 v) := by
  refine WP.block_intro (s.set 1 (BitVec.ofNat 64 v), []) rfl ?_
  have hE : Eff [] s (s.set 1 (BitVec.ofNat 64 v)) :=
    eff_of_mem (by simp [State.set, Function.update_of_ne]) (by simp [State.set, Function.update_of_ne])
      rfl rfl rfl rfl
  exact ⟨h.frm hE.frm, hE, by simp [State.set]⟩

theorem decode_R2p : decode p (R * R % p) = ((2 ^ 384 : ℕ) : F) := by
  unfold decode R
  rw [ZMod.natCast_mod, Nat.cast_mul, mul_assoc, ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_p 384), mul_one]

theorem decode_timesR (x : ℕ) : decode p (x * R % p) = (x : F) := by
  unfold decode R
  rw [ZMod.natCast_mod, Nat.cast_mul, mul_assoc, ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_p 384), mul_one]

theorem dp_eq_zero_iff {s : State} {i : ℕ} (h : sv s i < p) : dp s i = 0 ↔ sv s i = 0 :=
  decode_p_eq_zero_iff _ h

theorem final_ok (s : State) (h : Inv s) (R₁ : Point) (hR : PtAt s 0 R₁) (hr : sv s sR < n)
    (hr2 : sv s sR2P = R * R % p) (hnm : sv s sNm = n * R % p) :
    WP isa final s (fun q => Inv q ∧ Keep ptW s q ∧
      q.r 1 = BitVec.ofNat 64 (if finalOk R₁ (sv s sR) then 1 else 0)) := by
  have hR' : Jrep (dp s 0) (dp s 1) (dp s 2) R₁ := hR.rep
  have hrp : sv s sR < p := lt_trans hr n_lt_p
  have hu := ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_p 384)
  unfold final
  apply ifZero_wp 2 _ _ s h (by decide)
  · intro hz q hI hE _
    have hZ : dp s 2 = 0 := by unfold dp; rw [hz]; simp [decode]
    have h0 : R₁ = 0 := (jrep_zero_iff hZ).1 hR'
    refine WP.mono (ret_ok 0 q hI) ?_
    rintro q' ⟨hI', hE', h1⟩
    refine ⟨hI', (hE.keep'.trans hE'.keep').mono (by simp), ?_⟩
    rw [h1, h0]; rfl
  intro hz q hI hE _
  have hZ : dp s 2 ≠ 0 := fun h0 => hz ((dp_eq_zero_iff (hR.red 2 (by decide))).1 h0)
  have hq : ∀ i < nSlots, sv q i = sv s i := eff_nil_sv hE
  have hFI := finalOk_iff hR' hZ hr
  apply WP.seq
  have hred : ∀ i ∈ [sR, 2, 0], i < nSlots ∧ sv q i < p := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by decide, by rw [hq _ (by decide)]; exact hrp⟩
    · exact ⟨by decide, by rw [hq _ (by decide)]; exact hR.red 2 (by decide)⟩
    · exact ⟨by decide, by rw [hq _ (by decide)]; exact hR.red 0 (by decide)⟩
  refine WP.mono (pprog_ok [.mul 6 sR sR2P, .mul 7 2 2, .mul 8 6 7, .sub 9 0 8] [sR, 2, 0] q hI
    (by decide) hred) ?_
  rintro q1 ⟨hI1, hE1, hr1, hv1⟩
  have hu' : ((2 ^ 384 : ℕ) : F)⁻¹ * ((2 ^ 384 : ℕ) : F) = 1 := by rw [mul_comm]; exact hu
  have dR : decode p (sv q sR) * decode p (sv q sR2P) = (sv s sR : F) := by
    rw [hq _ (by decide), hq _ (by decide), hr2, decode_R2p]; unfold decode
    rw [mul_assoc, hu', mul_one]
  have v9 : dp q1 9 = dp s 0 - (sv s sR : F) * dp s 2 ^ 2 := by
    have := hv1 9 (by decide)
    simp (config := {decide := true}) only [FProg.run, FOp.run, Function.update_apply, sR, sR2P,
      ite_true, ite_false] at this
    unfold dp; rw [this, show (26 : ℕ) = sR from rfl, show (29 : ℕ) = sR2P from rfl, dR,
      hq 0 (by decide), hq 2 (by decide)]; ring
  have v7 : dp q1 7 = dp s 2 ^ 2 := by
    have := hv1 7 (by decide)
    simp (config := {decide := true}) only [FProg.run, FOp.run, Function.update_apply, sR, sR2P,
      ite_true, ite_false] at this
    unfold dp; rw [this, hq 2 (by decide)]; ring
  have v8 : dp q1 8 = (sv s sR : F) * dp s 2 ^ 2 := by
    have := hv1 8 (by decide)
    simp (config := {decide := true}) only [FProg.run, FOp.run, Function.update_apply, sR, sR2P,
      ite_true, ite_false] at this
    unfold dp; rw [this, show (26 : ℕ) = sR from rfl, show (29 : ℕ) = sR2P from rfl, dR,
      hq 2 (by decide)]; ring
  have hq1 : ∀ i < nSlots, i ∉ [6, 7, 8, 9] → sv q1 i = sv s i := fun i hi hn =>
    (hE1.keep i hi (by simpa [FProg.writes, FOp.dst] using hn)).trans (hq i hi)
  have hK1 : Keep [6, 7, 8, 9] s q1 := ⟨hE.frm.trans hE1.frm, hq1⟩
  apply ifZero_wp 9 _ _ q1 hI1 (by decide)
  · intro h9 q2 hI2 hE2 _
    have hz9 : dp q1 9 = 0 := by unfold dp; rw [h9]; simp [decode]
    rw [v9, sub_eq_zero] at hz9
    refine WP.mono (ret_ok 1 q2 hI2) ?_
    rintro q' ⟨hI', hE', h1⟩
    refine ⟨hI', ((hK1.trans hE2.keep').trans hE'.keep').mono (by simp [ptW]), ?_⟩
    rw [h1, if_pos (hFI.2 (Or.inl hz9))]
  intro h9 q2 hI2 hE2 _
  have hnz9 : dp s 0 ≠ (sv s sR : F) * dp s 2 ^ 2 := by
    intro e; apply h9; rw [← dp_eq_zero_iff (hr1 9 (by simp [FProg.writes, FOp.dst])), v9, e, sub_self]
  have hq2 : ∀ i < nSlots, sv q2 i = sv q1 i := eff_nil_sv hE2
  apply WP.seq
  obtain ⟨q3, hq3, hm3, hrd3, hwr3, hl3, h103, hr3, hcf3⟩ := ltConst_exec sR cPmn 10 q2 hI2 (by decide) (by decide)
    (by decide) (by decide)
  refine WP.block_intro q3 hq3 ?_
  have hE3 : Eff [] q2 q3.1 := eff_of_mem (hr3 13 (by decide)) (hr3 14 (by decide)) hm3 hrd3 hwr3 hl3
  have hI3 := hI2.frm hE3.frm
  have hlt : sv q2 sR < cval q2 cPmn ↔ sv s sR + n < p := by
    rw [hI2.vals.hpmn, hq2 _ (by decide), hq1 _ (by decide) (by decide)]
    have := n_lt_p; omega
  have hq3 : ∀ i < nSlots, sv q3.1 i = sv q1 i := fun i hi => by rw [eff_nil_sv hE3 i hi, hq2 i hi]
  have hK3 : Keep [6, 7, 8, 9] s q3.1 := (hK1.trans (hE2.keep'.trans hE3.keep')).mono (by simp)
  have hcond : isa.eval (.nez 10) q3.1 = some (decide (sv s sR + n < p)) := by
    simp only [isa, eval, hcf3, h103]
    by_cases hc : sv s sR + n < p
    · rw [if_pos (hlt.2 hc)]; simp [hc]
    · rw [if_neg (fun h' => hc (hlt.1 h'))]; simp [hc]
  apply WP.ite _ hcond
  · intro hb
    have hc : sv s sR + n < p := by simpa using hb
    have hred' : ∀ i ∈ [sNm, 7, 8, 0], i < nSlots ∧ sv q3.1 i < p := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · refine ⟨by decide, ?_⟩
        rw [hK3.2 _ (by decide) (by decide), hnm]; exact Nat.mod_lt _ (by decide)
      · exact ⟨by decide, by rw [hq3 _ (by decide)]; exact hr1 7 (by simp [FProg.writes, FOp.dst])⟩
      · exact ⟨by decide, by rw [hq3 _ (by decide)]; exact hr1 8 (by simp [FProg.writes, FOp.dst])⟩
      · exact ⟨by decide, by rw [hK3.2 _ (by decide) (by decide)]; exact hR.red 0 (by decide)⟩
    apply WP.seq
    refine WP.mono (pprog_ok [.mul 6 sNm 7, .add 8 8 6, .sub 9 0 8] [sNm, 7, 8, 0] q3.1 hI3 (by decide)
      hred') ?_
    rintro q4 ⟨hI4, hE4, hr4, hv4⟩
    have w9 : dp q4 9 = dp s 0 - ((sv s sR : F) * dp s 2 ^ 2 + (n : F) * dp s 2 ^ 2) := by
      have := hv4 9 (by decide)
      simp (config := {decide := true}) only [FProg.run, FOp.run, Function.update_apply, sNm,
        ite_true, ite_false] at this
      have e34 : decode p (sv q3.1 34) = (n : F) := by
        rw [show (34 : ℕ) = sNm from rfl, hK3.2 _ (by decide) (by decide), hnm, decode_timesR]
      have e7 : decode p (sv q3.1 7) = dp s 2 ^ 2 := by rw [hq3 _ (by decide)]; exact v7
      have e8 : decode p (sv q3.1 8) = (sv s sR : F) * dp s 2 ^ 2 := by rw [hq3 _ (by decide)]; exact v8
      have e0 : decode p (sv q3.1 0) = dp s 0 := by rw [hK3.2 _ (by decide) (by decide)]; rfl
      unfold dp at e7 e8 ⊢; rw [this, e34, e7, e8, e0]; unfold dp; ring
    have hK4 : Keep ptW s q4 := (hK3.trans hE4.keep').mono (by simp [ptW, FProg.writes, FOp.dst])
    apply ifZero_wp 9 _ _ q4 hI4 (by decide)
    · intro h9' q5 hI5 hE5 _
      have hz : dp q4 9 = 0 := by unfold dp; rw [h9']; simp [decode]
      rw [w9, sub_eq_zero] at hz
      refine WP.mono (ret_ok 1 q5 hI5) ?_
      rintro q' ⟨hI', hE', h1⟩
      refine ⟨hI', ((hK4.trans hE5.keep').trans hE'.keep').mono (by simp), ?_⟩
      rw [h1, if_pos (hFI.2 (Or.inr ⟨hc, by rw [hz]; push_cast; ring⟩))]
    · intro h9' q5 hI5 hE5 _
      have hz : dp s 0 ≠ ((sv s sR + n : ℕ) : F) * dp s 2 ^ 2 := by
        intro e; apply h9'
        rw [← dp_eq_zero_iff (hr4 9 (by simp [FProg.writes, FOp.dst])), w9, e]; push_cast; ring
      refine WP.mono (ret_ok 0 q5 hI5) ?_
      rintro q' ⟨hI', hE', h1⟩
      refine ⟨hI', ((hK4.trans hE5.keep').trans hE'.keep').mono (by simp), ?_⟩
      rw [h1, if_neg (fun hf => by
        rcases hFI.1 hf with e | ⟨-, e⟩
        · exact hnz9 e
        · exact hz e)]
  · intro hb
    have hc : ¬ sv s sR + n < p := by simpa using hb
    refine WP.mono (ret_ok 0 q3.1 hI3) ?_
    rintro q' ⟨hI', hE', h1⟩
    refine ⟨hI', (hK3.trans hE'.keep').mono (by simp [ptW]), ?_⟩
    rw [h1, if_neg (fun hf => by
      rcases hFI.1 hf with e | ⟨e, -⟩
      · exact hnz9 e
      · exact hc e)]

end CC.P384
