import ClaudeCrypto.P384.Steps

/-!
# Point doubling and addition (with all special cases) on frame slots
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- Decoded value of slot `i` in `𝔽_p`. -/
def dp (s : State) (i : Nat) : F := decode p (sv s i)

/-- Slots `a, a+1, a+2` hold (reduced, Montgomery-form) Jacobian coordinates of `P`. -/
def PtAt (s : State) (a : Nat) (P : Point) : Prop :=
  (∀ k < 3, sv s (a + k) < p) ∧ Jrep (dp s a) (dp s (a + 1)) (dp s (a + 2)) P

-- (a `structure` here makes elaboration run out of memory)
theorem PtAt.red {s : State} {a : Nat} {P : Point} (h : PtAt s a P) : ∀ k < 3, sv s (a + k) < p := h.1
theorem PtAt.rep {s : State} {a : Nat} {P : Point} (h : PtAt s a P) :
    Jrep (dp s a) (dp s (a + 1)) (dp s (a + 2)) P := h.2

theorem PtAt.congr {s q : State} {a b : Nat} {P : Point} (h : PtAt s a P)
    (he : ∀ k < 3, sv q (b + k) = sv s (a + k)) : PtAt q b P := by
  have e0 := he 0 (by decide); have e1 := he 1 (by decide); have e2 := he 2 (by decide)
  simp only [Nat.add_zero] at e0
  refine ⟨fun k hk => by rw [he k hk]; exact h.red k hk, ?_⟩
  unfold dp; rw [e0, e1, e2]; exact h.rep

theorem PtAt.of_eff {s q : State} {W : List Nat} {a : Nat} {P : Point} (h : PtAt s a P) (hE : Eff W s q)
    (ha : a + 3 ≤ nSlots) (hW : ∀ k < 3, a + k ∉ W) : PtAt q a P :=
  h.congr fun k hk => hE.keep _ (by omega) (hW k hk)

/-- The slots `0 … 14` used by the point operations. -/
def ptW : List Nat := List.range 15

theorem mem_ptW {i : Nat} : i ∈ ptW ↔ i < 15 := by simp [ptW]

/-! ## Doubling -/

theorem dbl_ok (s : State) (h : Inv s) (P : Point) (hP : PtAt s 0 P) :
    WP isa (pcode (dblProg 0 1 2 6)) s (fun q => Inv q ∧ Eff ptW s q ∧ PtAt q 0 (2 • P)) := by
  have hred : ∀ i ∈ [0, 1, 2], i < nSlots ∧ sv s i < p := by
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by decide, hP.red 0 (by decide)⟩
    · exact ⟨by decide, hP.red 1 (by decide)⟩
    · exact ⟨by decide, hP.red 2 (by decide)⟩
  refine WP.mono (pprog_ok _ [0, 1, 2] s h (by decide) hred) ?_
  rintro q ⟨hI, hE, hr, hv⟩
  refine ⟨hI, hE.mono (fun i hi => by
    rw [mem_ptW]; revert i; decide), fun k hk => hr _ (by revert k; decide), ?_⟩
  obtain ⟨e0, e1, e2⟩ := dbl_run (fun i => decode p (sv s i))
  have := jrep_dbl hP.rep
  unfold dp
  rw [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), e0, e1, e2]
  exact this

/-! ## Addition -/

/-- Slot values after `addPre`. -/
theorem addPre_ok (s : State) (h : Inv s) (hr : ∀ k < 6, sv s k < p) :
    WP isa (pcode (addPre 0 1 2 3 4 5 6)) s (fun q => Inv q ∧ Eff ptW s q ∧ (∀ k < 12, sv q k < p) ∧
      (∀ k < 6, sv q k = sv s k) ∧
      let X₁ := dp s 0; let Y₁ := dp s 1; let Z₁ := dp s 2; let X₂ := dp s 3; let Y₂ := dp s 4
      let Z₂ := dp s 5
      dp q 6 = Z₁ ^ 2 ∧ dp q 7 = Z₂ ^ 2 ∧ dp q 8 = X₁ * Z₂ ^ 2 ∧ dp q 9 = Y₁ * Z₂ * Z₂ ^ 2 ∧
      dp q 10 = X₂ * Z₁ ^ 2 - X₁ * Z₂ ^ 2 ∧ dp q 11 = 2 * (Y₂ * Z₁ * Z₁ ^ 2 - Y₁ * Z₂ * Z₂ ^ 2)) := by
  have hred : ∀ i ∈ [0, 1, 2, 3, 4, 5], i < nSlots ∧ sv s i < p := by
    intro i hi
    have : i < 6 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    exact ⟨by unfold nSlots; omega, hr i this⟩
  refine WP.mono (pprog_ok _ _ s h (by decide) hred) ?_
  rintro q ⟨hI, hE, hr', hv⟩
  obtain ⟨e6, e7, e8, e9, e10, e11, ek⟩ := addPre_run (fun i => decode p (sv s i))
  refine ⟨hI, hE.mono (fun i hi => by rw [mem_ptW]; revert i; decide),
    fun k hk => hr' _ (by revert k; decide), fun k hk => hE.keep k (by unfold nSlots; omega) (by
      revert k; decide), ?_⟩
  simp only [dp]
  rw [hv 6 (by decide), hv 7 (by decide), hv 8 (by decide), hv 9 (by decide), hv 10 (by decide),
    hv 11 (by decide), e6, e7, e8, e9, e10, e11]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `addPost` after `addPre`. -/
theorem addPost_ok (s : State) (h : Inv s) (hr : ∀ k < 12, sv s k < p) :
    WP isa (pcode (addPost 0 1 2 5 6)) s (fun q => Inv q ∧ Eff ptW s q ∧ (∀ k < 3, sv q k < p) ∧
      let Y₁ := dp s 1; let Z₁ := dp s 2; let Z₂ := dp s 5
      let Z1Z1 := dp s 6; let Z2Z2 := dp s 7; let U₁ := dp s 8; let S₁ := dp s 9; let H := dp s 10
      let rr := dp s 11
      let I := (2 * H) ^ 2
      let J := H * I
      let V := U₁ * I
      let X₃ := rr ^ 2 - J - 2 * V
      let Y₃ := rr * (V - X₃) - 2 * S₁ * J
      let Z₃ := ((Z₁ + Z₂) ^ 2 - Z1Z1 - Z2Z2) * H
      dp q 0 = X₃ ∧ dp q 1 = Y₃ ∧ dp q 2 = Z₃) := by
  have hred : ∀ i ∈ [0, 1, 2, 5, 6, 7, 8, 9, 10, 11], i < nSlots ∧ sv s i < p := by
    intro i hi
    have : i < 12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    exact ⟨by unfold nSlots; omega, hr i this⟩
  refine WP.mono (pprog_ok _ _ s h (by decide) hred) ?_
  rintro q ⟨hI, hE, hr', hv⟩
  obtain ⟨e0, e1, e2⟩ := addPost_run (fun i => decode p (sv s i))
  refine ⟨hI, hE.mono (fun i hi => by rw [mem_ptW]; revert i; decide),
    fun k hk => hr' _ (by revert k; decide), ?_⟩
  simp only [dp]
  rw [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), e0, e1, e2]
  exact ⟨rfl, rfl, rfl⟩

theorem copy3_exec (d a : Nat) (s : State) (h : Inv s) (hd : d + 3 ≤ nSlots) (ha : a + 3 ≤ nSlots)
    (hda : a + 3 ≤ d ∨ d + 3 ≤ a) :
    ∃ q, execBlock isa (copy3 d a) s = some q ∧ Eff [d, d + 1, d + 2] s q.1 ∧
      (∀ k < 3, sv q.1 (d + k) = sv s (a + k)) ∧ RegsExcept [9] s q.1 ∧ q.1.cf = s.cf := by
  obtain ⟨q1, hq1, E1, v1, r1, c1, -⟩ := copySlot_exec d a s h (by omega) (by omega)
  have I1 := h.frm E1.frm
  obtain ⟨q2, hq2, E2, v2, r2, c2, -⟩ := copySlot_exec (d + 1) (a + 1) q1.1 I1 (by omega) (by omega)
  have I2 := I1.frm E2.frm
  obtain ⟨q3, hq3, E3, v3, r3, c3, -⟩ := copySlot_exec (d + 2) (a + 2) q2.1 I2 (by omega) (by omega)
  obtain ⟨q12, hq12, e12⟩ := exec_app hq1 hq2
  obtain ⟨q, hq, e⟩ := exec_app hq12 (by rw [e12]; exact hq3)
  refine ⟨q, hq, e ▸ ((E1.trans E2).trans E3 |>.mono (by simp)), fun k hk => ?_,
    e ▸ ((r1.trans r2).trans r3 |>.mono (by simp)), by rw [e, c3, c2, c1]⟩
  rw [e]
  · have ne : ∀ j < 3, ∀ i < 3, d + j ≠ a + i := by intro j _ i _; omega
    interval_cases k
    · rw [Nat.add_zero, E3.keep d (by omega) (by simp), E2.keep d (by omega) (by simp), v1, Nat.add_zero]
    · rw [E3.keep (d + 1) (by omega) (by simp), v2, E1.keep (a + 1) (by omega) (by simp; omega)]
    · rw [v3, E2.keep (a + 2) (by omega) (by simp; omega), E1.keep (a + 2) (by omega) (by simp; omega)]

theorem dp_congr {s q : State} {i : Nat} (h : sv q i = sv s i) : dp q i = dp s i := by unfold dp; rw [h]

theorem eff_nil_sv {s q : State} (hE : Eff [] s q) (i : Nat) (hi : i < nSlots) : sv q i = sv s i :=
  hE.keep i hi (by simp)

theorem zeroSlot2_ok (s : State) (h : Inv s) (X Y : F) (hr : ∀ k < 3, sv s k < p) :
    WP isa (.block (zeroSlot 2)) s (fun q => Inv q ∧ Eff ptW s q ∧ PtAt q 0 0) := by
  apply block_wp (zeroSlot_exec 2 s h (by decide))
  rintro q ⟨E, v, -⟩
  have k0 := E.keep 0 (by decide) (by decide)
  have k1 := E.keep 1 (by decide) (by decide)
  refine ⟨h.frm E.frm, E.mono (by decide), ⟨fun k hk => ?_, ?_⟩⟩
  · interval_cases k
    · rw [k0]; exact hr 0 (by decide)
    · rw [k1]; exact hr 1 (by decide)
    · rw [v]; exact (by decide : 0 < p)
  · have : dp q.1 2 = 0 := by unfold dp; rw [v]; simp [decode]
    rw [this]; exact jrep_zero _ _

/-- Accumulator (slots 0–2) `+=` operand (slots 3–5), in all cases. -/
theorem addCode_ok (s : State) (h : Inv s) (P Q : Point) (hP : PtAt s 0 P) (hQ : PtAt s 3 Q) :
    WP isa addCode s (fun q => Inv q ∧ Eff ptW s q ∧ PtAt q 0 (P + Q)) := by
  have hP' : Jrep (dp s 0) (dp s 1) (dp s 2) P := hP.rep
  have hQ' : Jrep (dp s 3) (dp s 4) (dp s 5) Q := hQ.rep
  have JA := jrep_add hP' hQ'
  have hr6 : ∀ k < 6, sv s k < p := fun k hk => by
    rcases Nat.lt_or_ge k 3 with h3 | h3
    · have := hP.red k h3; rwa [Nat.zero_add] at this
    · have := hQ.red (k - 3) (by omega); rwa [show 3 + (k - 3) = k by omega] at this
  unfold addCode
  apply ifZero_wp 2 _ _ s h (by decide)
  · -- `P = 0`: the result is `Q`
    intro hz q hI hE _
    apply block_wp (copy3_exec 0 3 q hI (by decide) (by decide) (by decide))
    rintro q' ⟨E', v', -, -⟩
    refine ⟨hI.frm E'.frm, (hE.trans E').mono (by decide), ?_⟩
    have hZ : dp s 2 = 0 := by unfold dp; rw [hz]; simp [decode]
    rw [JA.1 hZ]
    exact hQ.congr fun k hk => by
      have := v' k hk; simp only [Nat.zero_add] at this ⊢
      rw [this, eff_nil_sv hE _ (by unfold nSlots; omega)]
  intro hz1 q hI hE _
  have hZ1 : dp s 2 ≠ 0 := fun h0 => hz1 ((decode_p_eq_zero_iff _ (hP.red 2 (by decide))).mp h0)
  have hq : ∀ k < nSlots, sv q k = sv s k := eff_nil_sv hE
  apply ifZero_wp 5 _ _ q hI (by decide)
  · -- `Q = 0`: the result is `P`
    intro hz q2 hI2 hE2 _
    apply WP.block_nil
    refine ⟨hI2, (hE.trans hE2).mono (by decide), ?_⟩
    have hZ : dp s 5 = 0 := by unfold dp; rw [← hq 5 (by decide), hz]; simp [decode]
    rw [JA.2.1 hZ]
    exact hP.congr fun k hk => by rw [eff_nil_sv hE2 _ (by unfold nSlots; omega), hq _ (by unfold nSlots; omega)]
  intro hz2 q2 hI2 hE2 _
  have hZ2 : dp s 5 ≠ 0 := fun h0 => hz2 (by
    rw [hq 5 (by decide)]; exact (decode_p_eq_zero_iff _ (hr6 5 (by decide))).mp h0)
  have hq2 : ∀ k < nSlots, sv q2 k = sv s k := fun k hk => (eff_nil_sv hE2 k hk).trans (hq k hk)
  have d2 : ∀ k < 6, dp q2 k = dp s k := fun k hk => dp_congr (hq2 k (by unfold nSlots; omega))
  apply WP.seq
  refine WP.mono (addPre_ok q2 hI2 (fun k hk => by rw [hq2 k (by unfold nSlots; omega)]; exact hr6 k hk)) ?_
  rintro q3 ⟨hI3, hE3, hr3, hk3, v6, v7, v8, v9, v10, v11⟩
  have d3 : ∀ k < 6, dp q3 k = dp s k := fun k hk => (dp_congr (hk3 k hk)).trans (d2 k hk)
  simp only [d2 0 (by decide), d2 1 (by decide), d2 2 (by decide), d2 3 (by decide), d2 4 (by decide),
    d2 5 (by decide)] at v6 v7 v8 v9 v10 v11
  have E3 : Eff ptW s q3 := ((hE.trans hE2).trans hE3).mono (by decide)
  apply ifZero_wp 10 _ _ q3 hI3 (by decide)
  · intro hH q4 hI4 hE4 _
    have hH' : dp q3 10 = 0 := by unfold dp; rw [hH]; simp [decode]
    rw [v10] at hH'
    have hq4 : ∀ k < nSlots, sv q4 k = sv q3 k := eff_nil_sv hE4
    apply ifZero_wp 11 _ _ q4 hI4 (by decide)
    · -- `P = Q`: double
      intro hR q5 hI5 hE5 _
      have hR' : dp q3 11 = 0 := by unfold dp; rw [← hq4 11 (by decide), hR]; simp [decode]
      rw [v11] at hR'
      have hPQ := JA.2.2.2.1 hZ1 hZ2 hH' hR'
      have hq5 : ∀ k < nSlots, sv q5 k = sv q3 k := fun k hk => (eff_nil_sv hE5 k hk).trans (hq4 k hk)
      have hP5 : PtAt q5 0 P := hP.congr fun k hk => by
        rw [hq5 _ (by unfold nSlots; omega), hk3 _ (by omega), hq2 _ (by unfold nSlots; omega)]
      refine WP.mono (dbl_ok q5 hI5 P hP5) ?_
      rintro q6 ⟨hI6, hE6, hP6⟩
      refine ⟨hI6, ((E3.trans hE4).trans (hE5.trans hE6)).mono (by decide), ?_⟩
      rw [← hPQ, ← two_nsmul]; exact hP6
    · -- `P = -Q`: zero
      intro hR q5 hI5 hE5 _
      have hR' : dp q3 11 ≠ 0 := fun h0 => hR (by
        rw [hq4 11 (by decide)]; exact (decode_p_eq_zero_iff _ (hr3 11 (by decide))).mp h0)
      rw [v11] at hR'
      have hPQ := JA.2.2.2.2 hZ1 hZ2 hH' hR'
      have hq5 : ∀ k < nSlots, sv q5 k = sv q3 k := fun k hk => (eff_nil_sv hE5 k hk).trans (hq4 k hk)
      refine WP.mono (zeroSlot2_ok q5 hI5 0 0 (fun k hk => by
        rw [hq5 k (by unfold nSlots; omega)]; exact hr3 k (by omega))) ?_
      rintro q6 ⟨hI6, hE6, hP6⟩
      refine ⟨hI6, ((E3.trans hE4).trans (hE5.trans hE6)).mono (by decide), ?_⟩
      rw [hPQ]; exact hP6
  · -- the generic case
    intro hH q4 hI4 hE4 _
    have hH' : dp q3 10 ≠ 0 := fun h0 => hH ((decode_p_eq_zero_iff _ (hr3 10 (by decide))).mp h0)
    rw [v10] at hH'
    have hq4 : ∀ k < nSlots, sv q4 k = sv q3 k := eff_nil_sv hE4
    have d4 : ∀ k < 12, dp q4 k = dp q3 k := fun k hk => dp_congr (hq4 k (by unfold nSlots; omega))
    refine WP.mono (addPost_ok q4 hI4 (fun k hk => by rw [hq4 k (by unfold nSlots; omega)]; exact hr3 k hk)) ?_
    rintro q5 ⟨hI5, hE5, hr5, e0, e1, e2⟩
    refine ⟨hI5, ((E3.trans hE4).trans hE5).mono (by decide), ⟨fun k hk => by rw [Nat.zero_add]; exact hr5 k hk, ?_⟩⟩
    show Jrep (dp q5 0) (dp q5 1) (dp q5 2) (P + Q)
    simp only [d4 1 (by decide), d4 2 (by decide), d4 5 (by decide), d4 6 (by decide), d4 7 (by decide),
      d4 8 (by decide), d4 9 (by decide), d4 10 (by decide), d4 11 (by decide),
      d3 1 (by decide), d3 2 (by decide), d3 5 (by decide), v6, v7, v8, v9, v10, v11] at e0 e1 e2
    rw [e0, e1, e2]
    exact JA.2.2.1 hZ1 hZ2 hH'

end CC.P384
