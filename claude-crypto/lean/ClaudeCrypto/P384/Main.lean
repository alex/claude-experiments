import ClaudeCrypto.P384.Setup

/-!
# The whole verification routine, in the limb IR

`main_ok`: from any state satisfying `MainPre`, `main` terminates with the
result of `CC.Spec.P384.verify` on the input bytes in register 1.
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

/-! ## The specification, case by case -/

section
variable (qx qy dg r s : List (BitVec 8))

theorem verify_of_not_qx (h : ¬ bytesToNat qx < p) : verify qx qy dg r s = false := by
  unfold verify decodePoint; rw [dif_neg (fun h' => h h'.1)]

theorem verify_of_not_qy (h : ¬ bytesToNat qy < p) : verify qx qy dg r s = false := by
  unfold verify decodePoint; rw [dif_neg (fun h' => h h'.2.1)]

theorem verify_of_not_rs (h : ¬ (1 ≤ bytesToNat r ∧ bytesToNat r < n ∧ 1 ≤ bytesToNat s ∧ bytesToNat s < n)) :
    verify qx qy dg r s = false := by
  unfold verify
  split
  · rfl
  · unfold verifyCore; rw [if_pos h]

theorem verify_of_not_curve (h : ¬ OnCurve (bytesToNat qx : F) (bytesToNat qy : F)) :
    verify qx qy dg r s = false := by
  unfold verify decodePoint; rw [dif_neg (fun h' => h h'.2.2)]

theorem verify_of_ok (h₁ : bytesToNat qx < p) (h₂ : bytesToNat qy < p)
    (hc : OnCurve (bytesToNat qx : F) (bytesToNat qy : F))
    (hrs : 1 ≤ bytesToNat r ∧ bytesToNat r < n ∧ 1 ≤ bytesToNat s ∧ bytesToNat s < n) :
    verify qx qy dg r s = finalOk
      ((((bytesToNat dg : ZMod n) * (bytesToNat s : ZMod n)⁻¹).val) • G +
        (((bytesToNat r : ZMod n) * (bytesToNat s : ZMod n)⁻¹).val) • mkPoint _ _ hc) (bytesToNat r) := by
  unfold verify decodePoint; rw [dif_pos ⟨h₁, h₂, hc⟩]
  show verifyCore _ _ _ _ = _
  unfold verifyCore; rw [if_neg (not_not.mpr hrs)]
  rfl

end

/-! ## Composition helpers -/

theorem Loaded.congr {s q q' : State} (h : Loaded s q) (he : ∀ i < nSlots, sv q' i = sv q i) : Loaded s q' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
  exact ⟨by rw [he _ (by decide)]; exact a1, by rw [he _ (by decide)]; exact a2, by rw [he _ (by decide)]; exact a3,
    by rw [he _ (by decide)]; exact a4, by rw [he _ (by decide)]; exact a5, by rw [he _ (by decide)]; exact a6,
    by rw [he _ (by decide)]; exact a7, by rw [he _ (by decide)]; exact a8, by rw [he _ (by decide)]; exact a9,
    by rw [he _ (by decide)]; exact a10, by rw [he _ (by decide)]; exact a11, by rw [he _ (by decide)]; exact a12,
    by rw [he _ (by decide)]; exact a13, by rw [he _ (by decide)]; exact a14, by rw [he _ (by decide)]; exact a15⟩

theorem check_ok (a c : Nat) (ok : LCode) (q : State) (hI : Inv q) (ha : a < nSlots) (hc : c + 48 ≤ constSize)
    (Q : State → Prop)
    (hyes : sv q a < cval q c → ∀ q', Inv q' → Eff [] q q' → WP isa ok q' Q)
    (hno : ¬ sv q a < cval q c → ∀ q', Inv q' → Eff [] q q' → WP isa (ret 0) q' Q) :
    WP isa (check (ltConst a c 10) ok) q Q := by
  unfold check
  obtain ⟨q1, hq1, hm, hrd, hwr, hl, h10, hr, hcf⟩ := ltConst_exec a c 10 q hI ha hc (by decide) (by decide)
  have hE : Eff [] q q1.1 := eff_of_mem (hr 13 (by decide)) (hr 14 (by decide)) hm hrd hwr hl
  have hI1 := hI.frm hE.frm
  apply WP.seq
  refine WP.block_intro q1 hq1 ?_
  by_cases hlt : sv q a < cval q c
  · have : isa.eval (.nez 10) q1.1 = some true := by
      simp only [isa, eval, hcf, h10, if_pos hlt]; decide
    exact WP.ite true this (fun _ => hyes hlt _ hI1 hE) (fun h => absurd h (by decide))
  · have : isa.eval (.nez 10) q1.1 = some false := by
      simp only [isa, eval, hcf, h10, if_neg hlt]; decide
    exact WP.ite false this (fun h => absurd h (by decide)) (fun _ => hno hlt _ hI1 hE)

theorem fail_ok (s q : State) (hI : Inv q) (hO : Out s q) (hv : verifyMem s.mem (s.r 5) (s.r 4) (s.r 0) = false) :
    WP isa (ret 0) q (MainPost s) := by
  refine WP.mono (ret_ok 0 q hI) ?_
  rintro q' ⟨-, hE, h1⟩
  have hO' := hO.frm hE.frm
  exact ⟨by rw [h1, hv]; rfl, hO'.r14, hO'.rd, hO'.wr, hO'.labels, hO'.agree⟩

theorem decode_Rp : decode p (R % p) = 1 := by
  unfold decode R
  rw [ZMod.natCast_mod, ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_p 384)]

/-! ## Public-key validation -/

theorem mulR2_p (q : State) (a : Nat) (hr2 : sv q sR2P = R * R % p) :
    decode p (sv q a) * decode p (sv q sR2P) = (sv q a : F) := by
  have hu := ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_p 384)
  have hu' : ((2 ^ 384 : ℕ) : F)⁻¹ * ((2 ^ 384 : ℕ) : F) = 1 := by rw [mul_comm]; exact hu
  rw [hr2, decode_R2p]; unfold decode; rw [mul_assoc, hu', mul_one]

theorem onCurve_ok (q : State) (hI : Inv q) (hqx : sv q sQx < p) (hqy : sv q sQy < p)
    (hr2 : sv q sR2P = R * R % p) (hb : sv q sB = b * R % p) :
    WP isa (pcode onCurveProg) q (fun q' => Inv q' ∧ Eff [sQ, sQ + 1, 6, 7, 8, 9] q q' ∧
      sv q' sQ < p ∧ sv q' (sQ + 1) < p ∧ sv q' 9 < p ∧ dp q' sQ = (sv q sQx : F) ∧
      dp q' (sQ + 1) = (sv q sQy : F) ∧ (dp q' 9 = 0 ↔ OnCurve (sv q sQx : F) (sv q sQy : F))) := by
  have hred : ∀ i ∈ [sQx, sQy, sB], i < nSlots ∧ sv q i < p := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by decide, hqx⟩
    · exact ⟨by decide, hqy⟩
    · exact ⟨by decide, by rw [hb]; exact Nat.mod_lt _ (by decide)⟩
  refine WP.mono (pprog_ok onCurveProg [sQx, sQy, sB] q hI (by decide) hred) ?_
  rintro q' ⟨hI', hE, hr, hv⟩
  have eX := mulR2_p q sQx hr2
  have eY := mulR2_p q sQy hr2
  have eB : decode p (sv q sB) = (b : F) := by rw [hb, decode_timesR]
  have v18 := hv 18 (by decide)
  have v19 := hv 19 (by decide)
  have v9 := hv 9 (by decide)
  simp (config := {decide := true}) only [onCurveProg, FProg.run, FOp.run, Function.update_apply, sQ, sQx,
    sQy, sR2P, sB, ite_true, ite_false] at v18 v19 v9
  simp only [show (35 : ℕ) = sQx from rfl, show (36 : ℕ) = sQy from rfl, show (29 : ℕ) = sR2P from rfl,
    show (30 : ℕ) = sB from rfl, eX, eY, eB] at v18 v19 v9
  refine ⟨hI', hE.mono (by simp [onCurveProg, FProg.writes, FOp.dst, sQ, sQx, sQy, sB, sR2P]),
    hr sQ (by simp [onCurveProg, FProg.writes, FOp.dst]), hr (sQ + 1) (by simp [onCurveProg, FProg.writes, FOp.dst]),
    hr 9 (by simp [onCurveProg, FProg.writes, FOp.dst]), v18, v19, ?_⟩
  unfold dp; rw [v9, sub_eq_zero]; unfold OnCurve
  constructor <;> intro e <;> linear_combination e

theorem ptAt_affine (q : State) (a : Nat) (x y : F) (hc : OnCurve x y) (hr : ∀ k < 3, sv q (a + k) < p)
    (hx : dp q a = x) (hy : dp q (a + 1) = y) (h1 : sv q (a + 2) = R % p) : PtAt q a (mkPoint x y hc) := by
  refine ⟨hr, ?_⟩
  have : dp q (a + 2) = 1 := by unfold dp; rw [h1]; exact decode_Rp
  rw [hx, hy, this]; exact jrep_affine hc

/-! ## The main theorem -/

theorem main_ok (s : State) (h : MainPre s) : WP isa main s (MainPost s) := by
  have hvm : verifyMem s.mem (s.r 5) (s.r 4) (s.r 0) = verify (inBytes s.mem (s.r 5) 48)
      (inBytes s.mem (s.r 5 + 48#64) 48) (inBytes s.mem (s.r 4) 48) (inBytes s.mem (s.r 0) 48)
      (inBytes s.mem (s.r 0 + 48#64) 48) := rfl
  have fail : ∀ q, Inv q → Out s q → verifyMem s.mem (s.r 5) (s.r 4) (s.r 0) = false →
      WP isa (ret 0) q (MainPost s) := fun q hI hO hv => fail_ok s q hI hO hv
  unfold main
  apply WP.seq
  refine WP.mono (setup_ok s h) ?_
  rintro q0 ⟨hI0, hO0, hL0⟩
  -- `x < p`
  refine check_ok sQx cP _ q0 hI0 (by decide) (by decide) _ ?_ ?_
  rotate_left
  · intro hlt q1 hI1 hE1
    rw [hI0.vals.hp, hL0.qx] at hlt
    exact fail q1 hI1 (hO0.frm hE1.frm) (verify_of_not_qx _ _ _ _ _ hlt)
  intro hqx q1 hI1 hE1
  rw [hI0.vals.hp, hL0.qx] at hqx
  have hO1 := hO0.frm hE1.frm
  have hL1 := hL0.congr (eff_nil_sv hE1)
  -- `y < p`
  refine check_ok sQy cP _ q1 hI1 (by decide) (by decide) _ ?_ ?_
  rotate_left
  · intro hlt q2 hI2 hE2
    rw [hI1.vals.hp, hL1.qy] at hlt
    exact fail q2 hI2 (hO1.frm hE2.frm) (verify_of_not_qy _ _ _ _ _ hlt)
  intro hqy q2 hI2 hE2
  rw [hI1.vals.hp, hL1.qy] at hqy
  have hO2 := hO1.frm hE2.frm
  have hL2 := hL1.congr (eff_nil_sv hE2)
  -- `r < n`
  refine check_ok sR cN _ q2 hI2 (by decide) (by decide) _ ?_ ?_
  rotate_left
  · intro hlt q3 hI3 hE3
    rw [hI2.vals.hn, hL2.r] at hlt
    exact fail q3 hI3 (hO2.frm hE3.frm) (verify_of_not_rs _ _ _ _ _ (fun hh => hlt hh.2.1))
  intro hrn q3 hI3 hE3
  rw [hI2.vals.hn, hL2.r] at hrn
  have hO3 := hO2.frm hE3.frm
  have hL3 := hL2.congr (eff_nil_sv hE3)
  -- `r ≠ 0`
  apply ifZero_wp sR _ _ q3 hI3 (by decide)
  · intro hz q4 hI4 hE4 _
    rw [hL3.r] at hz
    exact fail q4 hI4 (hO3.frm hE4.frm) (verify_of_not_rs _ _ _ _ _ (fun hh => by omega))
  intro hr0 q4 hI4 hE4 _
  rw [hL3.r] at hr0
  have hO4 := hO3.frm hE4.frm
  have hL4 := hL3.congr (eff_nil_sv hE4)
  -- `s < n`
  refine check_ok sS cN _ q4 hI4 (by decide) (by decide) _ ?_ ?_
  rotate_left
  · intro hlt q5 hI5 hE5
    rw [hI4.vals.hn, hL4.s] at hlt
    exact fail q5 hI5 (hO4.frm hE5.frm) (verify_of_not_rs _ _ _ _ _ (fun hh => hlt hh.2.2.2))
  intro hsn q5 hI5 hE5
  rw [hI4.vals.hn, hL4.s] at hsn
  have hO5 := hO4.frm hE5.frm
  have hL5 := hL4.congr (eff_nil_sv hE5)
  -- `s ≠ 0`
  apply ifZero_wp sS _ _ q5 hI5 (by decide)
  · intro hz q6 hI6 hE6 _
    rw [hL5.s] at hz
    exact fail q6 hI6 (hO5.frm hE6.frm) (verify_of_not_rs _ _ _ _ _ (fun hh => by omega))
  intro hs0 q6 hI6 hE6 _
  rw [hL5.s] at hs0
  have hO6 := hO5.frm hE6.frm
  have hL6 := hL5.congr (eff_nil_sv hE6)
  have hrs : 1 ≤ bytesToNat (inBytes s.mem (s.r 0) 48) ∧ bytesToNat (inBytes s.mem (s.r 0) 48) < n ∧
      1 ≤ bytesToNat (inBytes s.mem (s.r 0 + 48#64) 48) ∧ bytesToNat (inBytes s.mem (s.r 0 + 48#64) 48) < n :=
    ⟨by omega, hrn, by omega, hsn⟩
  -- the curve equation
  apply WP.seq
  refine WP.mono (onCurve_ok q6 hI6 (by rw [hL6.qx]; exact hqx) (by rw [hL6.qy]; exact hqy) hL6.r2p hL6.b) ?_
  rintro q7 ⟨hI7, hE7, hr18, hr19, hr9, hx7, hy7, hc7⟩
  rw [hL6.qx] at hx7 hc7
  rw [hL6.qy] at hy7 hc7
  have hO7 := hO6.frm hE7.frm
  have k7 : ∀ i < nSlots, i ∉ [sQ, sQ + 1, 6, 7, 8, 9] → sv q7 i = sv q6 i := hE7.keep
  apply ifZero_wp 9 _ _ q7 hI7 (by decide)
  rotate_left
  · intro hnz q8 hI8 hE8 _
    refine fail q8 hI8 (hO7.frm hE8.frm) (verify_of_not_curve _ _ _ _ _ (fun hc => hnz ?_))
    exact (dp_eq_zero_iff hr9).1 (hc7.2 hc)
  intro hz q8 hI8 hE8 _
  have hc : OnCurve (bytesToNat (inBytes s.mem (s.r 5) 48) : F) (bytesToNat (inBytes s.mem (s.r 5 + 48#64) 48) : F) := hc7.1 ((dp_eq_zero_iff hr9).2 hz)
  have hO8 := hO7.frm hE8.frm
  have k8 : ∀ i < nSlots, i ∉ [sQ, sQ + 1, 6, 7, 8, 9] → sv q8 i = sv q6 i := fun i hi hn =>
    (eff_nil_sv hE8 i hi).trans (k7 i hi hn)
  have hQ8 : PtAt q8 sQ (mkPoint _ _ hc) := by
    refine ptAt_affine q8 sQ _ _ hc (fun k hk => ?_) ?_ ?_ ?_
    · rw [eff_nil_sv hE8 _ (by unfold sQ nSlots; omega)]
      interval_cases k
      · exact hr18
      · exact hr19
      · rw [k7 _ (by decide) (by decide), hL6.q1]; exact Nat.mod_lt _ (by decide)
    · unfold dp; rw [eff_nil_sv hE8 _ (by decide)]; exact hx7
    · unfold dp; rw [eff_nil_sv hE8 _ (by decide)]; exact hy7
    · rw [k8 _ (by decide) (by decide), hL6.q1]
  have hG8 : PtAt q8 sG G := by
    refine ptAt_affine q8 sG _ _ G_on_curve (fun k hk => ?_) ?_ ?_ ?_
    · rw [k8 _ (by unfold sG nSlots; omega) (by simp [sG, sQ]; omega)]
      interval_cases k
      · rw [Nat.add_zero, hL6.gx]; exact Nat.mod_lt _ (by decide)
      · rw [hL6.gy]; exact Nat.mod_lt _ (by decide)
      · rw [hL6.g1]; exact Nat.mod_lt _ (by decide)
    · unfold dp; rw [k8 _ (by decide) (by decide), hL6.gx, decode_timesR]
    · unfold dp; rw [k8 _ (by decide) (by decide), hL6.gy, decode_timesR]
    · rw [k8 _ (by decide) (by decide), hL6.g1]
  -- scalars
  apply WP.seq
  refine WP.mono (scalars_ok q8 hI8 (by rw [k8 _ (by decide) (by decide), hL6.s]; exact hsn)
    (by rw [k8 _ (by decide) (by decide), hL6.s]; omega) (by rw [k8 _ (by decide) (by decide), hL6.r]; exact hrn)
    (by rw [k8 _ (by decide) (by decide), hL6.r2n]) (by rw [k8 _ (by decide) (by decide), hL6.oneN])
    (by rw [k8 _ (by decide) (by decide), hL6.exp])) ?_
  rintro q9 ⟨hI9, hK9, hu1, hu2⟩
  rw [k8 _ (by decide) (by decide), k8 _ (by decide) (by decide), hL6.e, hL6.s] at hu1
  rw [k8 _ (by decide) (by decide), k8 _ (by decide) (by decide), hL6.r, hL6.s] at hu2
  have hO9 := hO8.frm hK9.1
  -- `u₁·G + u₂·Q`
  apply WP.seq
  refine WP.mono (pointPart_ok q9 hI9 _ _
    (hG8.congr fun k hk => hK9.2 _ (by unfold sG nSlots; omega) (by simp [sG, sExp, sU1, sU2]; omega))
    (hQ8.congr fun k hk => hK9.2 _ (by unfold sQ nSlots; omega) (by simp [sQ, sExp, sU1, sU2]; omega))) ?_
  rintro q10 ⟨hI10, hK10, hP10⟩
  rw [hu1, hu2] at hP10
  have hO10 := hO9.frm hK10.1
  -- the comparison
  have e26 : sv q10 sR = bytesToNat (inBytes s.mem (s.r 0) 48) := by
    rw [hK10.2 _ (by decide) (by decide), hK9.2 _ (by decide) (by decide), k8 _ (by decide) (by decide), hL6.r]
  refine WP.mono (final_ok q10 hI10 _ hP10 (by rw [e26]; exact hrn)
    (by rw [hK10.2 _ (by decide) (by decide), hK9.2 _ (by decide) (by decide), k8 _ (by decide) (by decide),
      hL6.r2p])
    (by rw [hK10.2 _ (by decide) (by decide), hK9.2 _ (by decide) (by decide), k8 _ (by decide) (by decide),
      hL6.nm])) ?_
  rintro q11 ⟨-, hK11, h1⟩
  have hO11 := hO10.frm hK11.1
  refine ⟨?_, hO11.r14, hO11.rd, hO11.wr, hO11.labels, hO11.agree⟩
  rw [h1, hvm, verify_of_ok _ _ _ _ _ hqx hqy hc hrs, e26]

end CC.P384
