import ClaudeCrypto.P384.PointOps

/-!
# The scalar part: `u₁ = e·s⁻¹` and `u₂ = r·s⁻¹ (mod n)`
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

/-! ## Bits of a scalar shifted out of the top of a slot -/

theorem bit_step (E j : ℕ) (hj : j < 384) :
    E * 2 ^ j % 2 ^ 384 / 2 ^ 383 = E / 2 ^ (383 - j) % 2 ∧
    E / 2 ^ (383 - j) = 2 * (E / 2 ^ (384 - j)) + E / 2 ^ (383 - j) % 2 ∧
    2 * (E * 2 ^ j % 2 ^ 384) % 2 ^ 384 = E * 2 ^ (j + 1) % 2 ^ 384 := by
  have e1 : (2 : ℕ) ^ 384 = 2 ^ (384 - j) * 2 ^ j := by rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) ^ 383 = 2 ^ (383 - j) * 2 ^ j := by rw [← pow_add]; congr 1; omega
  have e3 : (2 : ℕ) ^ (384 - j) = 2 ^ (383 - j) * 2 := by rw [← pow_succ]; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Nat.mul_mod_mul_right, e2, Nat.mul_div_mul_right _ _ (by positivity), e3,
      Nat.mod_mul_right_div_self]
  · rw [e3, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (E / 2 ^ (383 - j)) 2
    omega
  · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; ring_nf

/-- Decoded value of slot `i` in `ZMod n`. -/
def dn (s : State) (i : Nat) : ZMod n := decode n (sv s i)

theorem Rn_unit : IsUnit ((2 ^ 384 : ℕ) : ZMod n) := Spec.Montgomery.isUnit_cast_of_coprime (coprime_two_pow_n 384)

theorem decode_R2n : decode n (R * R % n) = ((2 ^ 384 : ℕ) : ZMod n) := by
  unfold decode R
  rw [ZMod.natCast_mod, Nat.cast_mul, mul_assoc, ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_n 384), mul_one]

theorem decode_Rn : decode n (R % n) = 1 := by
  unfold decode R
  rw [ZMod.natCast_mod, ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_n 384)]

/-- A reduced slot whose decoded value is `y · R⁻¹` holds `y.val`. -/
theorem eq_val_of_decode {x : ℕ} {y : ZMod n} (hx : x < n)
    (h : decode n x = y * ((2 ^ 384 : ℕ) : ZMod n)⁻¹) : x = y.val := by
  have hu := ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_n 384)
  unfold decode at h
  have hu' : ((2 ^ 384 : ℕ) : ZMod n)⁻¹ * ((2 ^ 384 : ℕ) : ZMod n) = 1 := by rw [mul_comm]; exact hu
  have : (x : ZMod n) = y := by
    have := congrArg (· * ((2 ^ 384 : ℕ) : ZMod n)) h
    rwa [mul_assoc, mul_assoc, hu', mul_one, mul_one] at this
  rw [← this, ZMod.val_natCast_of_lt hx]

/-! ## Frame effects without the counter -/

/-- Like `Eff`, but the counter may change. -/
def Keep (W : List Nat) (s q : State) : Prop := Frm s q ∧ ∀ i < nSlots, i ∉ W → sv q i = sv s i

theorem Keep.trans {W₁ W₂ : List Nat} {s q u : State} (h1 : Keep W₁ s q) (h2 : Keep W₂ q u) :
    Keep (W₁ ++ W₂) s u :=
  ⟨h1.1.trans h2.1, fun i hi hw => by
    simp only [List.mem_append, not_or] at hw
    rw [h2.2 i hi hw.2, h1.2 i hi hw.1]⟩

theorem Keep.mono {W W' : List Nat} {s q : State} (h : Keep W s q) (hW : ∀ i ∈ W, i ∈ W') : Keep W' s q :=
  ⟨h.1, fun i hi hw => h.2 i hi (fun h' => hw (hW i h'))⟩

theorem Eff.keep' {W : List Nat} {s q : State} (h : Eff W s q) : Keep W s q := ⟨h.frm, h.keep⟩

theorem Keep.refl (s : State) : Keep [] s s := ⟨Frm.refl s, fun _ _ _ => rfl⟩

theorem ofNat_pred (m : ℕ) (hm : 0 < m) (hm' : m < 2 ^ 64) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem ofNat_ne_zero_iff (m : ℕ) (hm' : m < 2 ^ 64) : (BitVec.ofNat 64 m != 0) = decide (m ≠ 0) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; rfl
  · have h1 : BitVec.ofNat 64 m ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm'] at this
      simp at this; omega
    rw [show (BitVec.ofNat 64 m != 0) = true by simpa using h1]
    simp; omega

/-- The loop-back test after `cntDec`. -/
theorem cnt_cond {q : State} {m : ℕ} (hcf : q.cf = none) (h9 : q.r 9 = BitVec.ofNat 64 m) (hm : m < 2 ^ 64) :
    isa.eval (.nez 9) q = some (decide (m ≠ 0)) := by
  simp only [isa, eval, hcf, h9, ofNat_ne_zero_iff m hm]

/-- `ite (nez v)` on a bit. -/
theorem bit_cond {q : State} {v : Var} {b : ℕ} (hb : b < 2) (hcf : q.cf = none) (hv : q.r v = BitVec.ofNat 64 b) :
    isa.eval (.nez v) q = some (decide (b = 1)) := by
  simp only [isa, eval, hcf, hv]
  interval_cases b <;> rfl

/-! ## The inversion loop -/

/-- The invariant with `m` iterations left. -/
def ExpInv (s0 : State) (E m : Nat) (s : State) : Prop :=
  0 < m ∧ m ≤ 384 ∧ Inv s ∧ Keep [7, sExp] s0 s ∧ cnt s = BitVec.ofNat 64 m ∧
    sv s sExp = E * 2 ^ (384 - m) % 2 ^ 384 ∧ sv s 7 < n ∧ dn s 7 = dn s0 6 ^ (E / 2 ^ m)

theorem invLoop_ok (s0 : State) (E : Nat) (h6 : sv s0 6 < n) :
    ∀ m s, ExpInv s0 E m s → WP isa invLoop s (fun q => Inv q ∧ Keep [7, sExp] s0 q ∧ sv q 7 < n ∧
      dn q 7 = dn s0 6 ^ E) := by
  intro m s hs
  unfold invLoop
  refine WP.loop (M := isa) (ExpInv s0 E) ?_ m s hs
  clear hs s m
  intro m s ⟨hm0, hm, hI, hK, hc, hx, h7, hv⟩
  have h6s : sv s 6 = sv s0 6 := hK.2 6 (by decide) (by decide)
  obtain ⟨b1, b2, b3⟩ := bit_step E (384 - m) (by omega)
  simp only [show 383 - (384 - m) = m - 1 by omega, show 384 - (384 - m) = m by omega] at b1 b2
  simp only [show 384 - m + 1 = 384 - (m - 1) by omega] at b3
  set bit := E / 2 ^ (m - 1) % 2 with hbit
  have hbit2 : bit < 2 := Nat.mod_lt _ (by decide)
  -- square
  apply WP.seq
  refine WP.mono (nprog_ok [.mul 7 7 7] [7] s hI (by decide) (fun i hi => by
    simp only [List.mem_singleton] at hi; subst hi; exact ⟨by decide, h7⟩)) ?_
  rintro q1 ⟨hI1, hE1, hr1, hv1⟩
  have hv17 := hv1 7 (by decide)
  simp only [FProg.run, FOp.run, Function.update_self] at hv17
  have hx1 : sv q1 sExp = sv s sExp := hE1.keep sExp (by decide) (by decide)
  have h61 : sv q1 6 = sv s 6 := hE1.keep 6 (by decide) (by decide)
  -- next bit
  apply WP.seq
  obtain ⟨q2, hq2, hE2, hx2, hb2, -, hcf2⟩ :=
    topBit_exec sExp 10 q1 hI1 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.block_intro q2 hq2 ?_
  have hI2 := hI1.frm hE2.frm
  rw [hx1, hx, b1] at hb2
  rw [hx1, hx, b3] at hx2
  have h72 : sv q2.1 7 = sv q1 7 := hE2.keep 7 (by decide) (by decide)
  have h62 : sv q2.1 6 = sv s0 6 := (hE2.keep 6 (by decide) (by decide)).trans (h61.trans h6s)
  have hc2 : cnt q2.1 = BitVec.ofNat 64 m := hE2.cnt.trans (hE1.cnt.trans hc)
  -- conditional multiply
  have hmul : WP isa (.ite (.nez 10) (ncode [.mul 7 7 6]) (.block [])) q2.1 (fun q3 => Inv q3 ∧
      Eff [7] q2.1 q3 ∧ sv q3 7 < n ∧ dn q3 7 = dn q2.1 7 * dn s0 6 ^ bit) := by
    apply WP.ite _ (bit_cond hbit2 hcf2 hb2)
    · intro hb
      have hb1 : bit = 1 := by simpa using hb
      refine WP.mono (nprog_ok [.mul 7 7 6] [7, 6] q2.1 hI2 (by decide) (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨by decide, by rw [h72]; exact hr1 7 (by simp)⟩
        · exact ⟨by decide, by rw [h62]; exact h6⟩)) ?_
      rintro q3 ⟨hI3, hE3, hr3, hv3⟩
      have hv37 := hv3 7 (by decide)
      simp only [FProg.run, FOp.run, Function.update_self] at hv37
      refine ⟨hI3, hE3.mono (by simp [FProg.writes, FOp.dst]), hr3 7 (by simp [FProg.writes, FOp.dst]), ?_⟩
      rw [hb1, pow_one]; unfold dn; rw [hv37, h62]
    · intro hb
      have hb0 : bit = 0 := by simp at hb; omega
      apply WP.block_nil
      refine ⟨hI2, (Eff.refl _).mono (by simp), by rw [h72]; exact hr1 7 (by simp), ?_⟩
      rw [hb0, pow_zero, mul_one]
  apply WP.seq
  refine WP.mono hmul ?_
  rintro q3 ⟨hI3, hE3, hr3, hv3⟩
  obtain ⟨q4, hq4, hF4, hs4, hc4, h94, -, hcf4⟩ := cntDec_exec q3 hI3
  refine WP.block_intro q4 hq4 ?_
  have hc3 : cnt q3 = BitVec.ofNat 64 m := hE3.cnt.trans hc2
  rw [hc3, ofNat_pred m hm0 (by omega)] at hc4 h94
  have hK4 : Keep [7, sExp] s0 q4.1 :=
    (hK.trans (((hE1.keep'.trans hE2.keep').trans hE3.keep').trans (⟨hF4, fun i hi _ => hs4 i hi⟩ : Keep [] q3 q4.1))).mono (by simp [FProg.writes, FOp.dst])
  have hI4 := hI3.frm hF4
  have hx4 : sv q4.1 sExp = E * 2 ^ (384 - (m - 1)) % 2 ^ 384 := by
    rw [hs4 _ (by decide), hE3.keep sExp (by decide) (by decide), hx2]
  have hr4 : sv q4.1 7 < n := by rw [hs4 _ (by decide)]; exact hr3
  have hv4 : dn q4.1 7 = dn s0 6 ^ (E / 2 ^ (m - 1)) := by
    unfold dn; rw [hs4 _ (by decide)]
    change dn q3 7 = _
    rw [hv3]; unfold dn; rw [h72, hv17]
    change dn s 7 * dn s 7 * dn s0 6 ^ bit = _
    rw [hv, ← pow_add, ← pow_add, b2]; unfold dn; ring_nf
  by_cases hm1 : m - 1 = 0
  · left
    refine ⟨by rw [cnt_cond hcf4 h94 (by omega)]; simp [hm1], hI4, hK4, hr4, ?_⟩
    rw [hv4, hm1, pow_zero, Nat.div_one]
  · right
    refine ⟨by rw [cnt_cond hcf4 h94 (by omega)]; simp [hm1], m - 1, by omega,
      by omega, by omega, hI4, hK4, hc4, hx4, hr4, hv4⟩

/-! ## `u₁`, `u₂` -/

theorem n_lt_R : n < 2 ^ 384 := n_lt_two_pow_384

theorem pow_n_sub_two (a : ZMod n) (ha : a ≠ 0) : a ^ (n - 2) = a⁻¹ := by
  haveI := Fact.mk n_prime
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, show n - 2 + 1 = n - 1 by have := n_prime.two_le; omega]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem natCast_ne_zero_n {x : ℕ} (hx : x < n) (h0 : x ≠ 0) : (x : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; exact h0 (Nat.eq_zero_of_dvd_of_lt hd hx)

theorem scalars_ok (s : State) (h : Inv s) (hS : sv s sS < n) (hS0 : sv s sS ≠ 0) (hR : sv s sR < n)
    (hR2 : sv s sR2N = R * R % n) (hOne : sv s sOneN = R % n) (hExp : sv s sExp = n - 2) :
    WP isa scalars s (fun q => Inv q ∧ Keep [6, 7, sExp, sU1, sU2] s q ∧
      sv q sU1 = ((sv s sE : ZMod n) * (sv s sS : ZMod n)⁻¹).val ∧
      sv q sU2 = ((sv s sR : ZMod n) * (sv s sS : ZMod n)⁻¹).val) := by
  have hu := ZMod.coe_mul_inv_eq_one _ (coprime_two_pow_n 384)
  unfold scalars
  -- `slot 6 := s` (Montgomery form)
  apply WP.seq
  refine WP.mono (nprog_ok [.mul 6 sS sR2N] [sS] s h (by decide) (fun i hi => by
    simp only [List.mem_singleton] at hi; subst hi; exact ⟨by decide, hS⟩)) ?_
  rintro q1 ⟨hI1, hE1, hr1, hv1⟩
  have h61 : dn q1 6 = (sv s sS : ZMod n) := by
    have := hv1 6 (by decide)
    simp only [FProg.run, FOp.run, Function.update_self] at this
    unfold dn; rw [this, hR2, decode_R2n]; unfold decode
    rw [mul_assoc, mul_comm _ ((2 ^ 384 : ℕ) : ZMod n), hu, mul_one]
  have hr61 : sv q1 6 < n := hr1 6 (by simp [FProg.writes, FOp.dst])
  -- `slot 7 := 1`, counter
  apply WP.seq
  obtain ⟨qa, hqa, hEa, hva, -, -, -⟩ := copySlot_exec 7 sOneN q1 hI1 (by decide) (by decide)
  have hIa := hI1.frm hEa.frm
  obtain ⟨qb, hqb, hFb, hsb, hcb, -, -, -⟩ := cntInit_exec 384 qa.1 hIa
  obtain ⟨q2, hq2, e2⟩ := exec_app hqa hqb
  refine WP.block_intro q2 hq2 ?_
  have hI2 : Inv q2.1 := by rw [e2]; exact hIa.frm hFb
  have hK2 : Keep [6, 7] s q2.1 := by
    rw [e2]; exact ((hE1.keep'.trans hEa.keep').trans (⟨hFb, fun i hi _ => hsb i hi⟩ : Keep [] qa.1 qb.1)).mono
      (by simp [FProg.writes, FOp.dst])
  have hsv2 : ∀ i < nSlots, i ≠ 7 → sv q2.1 i = sv q1 i := fun i hi hne => by
    rw [e2, hsb i hi]; exact hEa.keep i hi (by simpa using hne)
  have h72 : sv q2.1 7 = R % n := by rw [e2, hsb 7 (by decide), hva, hE1.keep sOneN (by decide) (by decide), hOne]
  have hx2 : sv q2.1 sExp = n - 2 := by
    rw [hsv2 _ (by decide) (by decide), hE1.keep sExp (by decide) (by decide), hExp]
  -- the loop
  apply WP.seq
  have hinit : ExpInv q2.1 (n - 2) 384 q2.1 := by
    refine ⟨by decide, le_refl _, hI2, (Keep.refl _).mono (by simp), by rw [e2]; exact hcb, ?_, ?_, ?_⟩
    · rw [hx2, Nat.sub_self, pow_zero, mul_one, Nat.mod_eq_of_lt (by have := n_lt_R; omega)]
    · rw [h72]; exact Nat.mod_lt _ (by decide)
    · rw [Nat.div_eq_of_lt (by have := n_lt_R; omega), pow_zero]
      unfold dn; rw [h72]; exact decode_Rn
  refine WP.mono (invLoop_ok q2.1 (n - 2) (by rw [hsv2 6 (by decide) (by decide)]; exact hr61) 384 q2.1 hinit) ?_
  rintro q3 ⟨hI3, hK3, hr3, hv3⟩
  have h62 : dn q2.1 6 = (sv s sS : ZMod n) := by unfold dn; rw [hsv2 6 (by decide) (by decide)]; exact h61
  rw [h62, pow_n_sub_two _ (natCast_ne_zero_n hS hS0)] at hv3
  -- `u₁`, `u₂`
  have hK3' : Keep [6, 7, sExp] s q3 := (hK2.trans hK3).mono (by simp)
  refine WP.mono (nprog_ok [.mul sU1 7 sE, .mul sU2 7 sR] [7] q3 hI3 (by decide) (fun i hi => by
    simp only [List.mem_singleton] at hi; subst hi; exact ⟨by decide, hr3⟩)) ?_
  rintro q4 ⟨hI4, hE4, hr4, hv4⟩
  have eE : sv q3 sE = sv s sE := hK3'.2 sE (by decide) (by decide)
  have eR : sv q3 sR = sv s sR := hK3'.2 sR (by decide) (by decide)
  refine ⟨hI4, (hK3'.trans hE4.keep').mono (by simp [FProg.writes, FOp.dst]), ?_, ?_⟩
  · apply eq_val_of_decode (hr4 sU1 (by simp [FProg.writes, FOp.dst]))
    have := hv4 sU1 (by decide)
    simp only [FProg.run, FOp.run] at this
    rw [Function.update_of_ne (by decide : sU1 ≠ sU2), Function.update_self] at this
    rw [this]
    change dn q3 7 * decode n (sv q3 sE) = _
    rw [hv3, eE]; unfold decode; ring
  · apply eq_val_of_decode (hr4 sU2 (by simp [FProg.writes, FOp.dst]))
    have := hv4 sU2 (by decide)
    simp only [FProg.run, FOp.run] at this
    rw [Function.update_self] at this
    rw [this]
    change dn q3 7 * decode n (sv q3 sR) = _
    rw [hv3, eR]; unfold decode; ring

end CC.P384
