import ClaudeCrypto.P384.Prims

/-!
# Composition rules for the pieces of the P-384 program
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- A field program, in terms of `Inv`/`Eff`. -/
theorem fprog_ok (offN offMp N : Nat) (hL : ∀ s, Inv s → Layout offN offMp 0 nSlots N s)
    (ops : List FOp) (init : List Nat) (s : State) (h : Inv s) (hwf : FProg.wf nSlots ops init = true)
    (hred : ∀ i ∈ init, i < nSlots ∧ sv s i < N) :
    WP isa (FProg.code offN offMp 0 ops) s (fun q => Inv q ∧ Eff (FProg.writes ops) s q ∧
      (∀ i ∈ init ++ FProg.writes ops, sv q i < N) ∧
      ∀ i < nSlots, decode N (sv q i) = FProg.run ops (fun i => decode N (sv s i)) i) := by
  refine WP.mono (prog_ok offN offMp 0 nSlots N ops init s hwf (hL s h) hred) ?_
  intro q hq
  have hf : Frm s q := frm_of_agree hq.r13 hq.r14 hq.rd hq.wr hq.labels hq.agree
  exact ⟨h.frm hf, ⟨hf, hq.others, cnt_of_agree hq.r14 hq.agree⟩, hq.red, hq.vals⟩

theorem pprog_ok (ops : List FOp) (init : List Nat) (s : State) (h : Inv s)
    (hwf : FProg.wf nSlots ops init = true) (hred : ∀ i ∈ init, i < nSlots ∧ sv s i < p) :
    WP isa (pcode ops) s (fun q => Inv q ∧ Eff (FProg.writes ops) s q ∧
      (∀ i ∈ init ++ FProg.writes ops, sv q i < p) ∧
      ∀ i < nSlots, decode p (sv q i) = FProg.run ops (fun i => decode p (sv s i)) i) :=
  fprog_ok cP cMpP p (fun _ h => h.layoutP) ops init s h hwf hred

theorem nprog_ok (ops : List FOp) (init : List Nat) (s : State) (h : Inv s)
    (hwf : FProg.wf nSlots ops init = true) (hred : ∀ i ∈ init, i < nSlots ∧ sv s i < n) :
    WP isa (ncode ops) s (fun q => Inv q ∧ Eff (FProg.writes ops) s q ∧
      (∀ i ∈ init ++ FProg.writes ops, sv q i < n) ∧
      ∀ i < nSlots, decode n (sv q i) = FProg.run ops (fun i => decode n (sv s i)) i) :=
  fprog_ok cN cMpN n (fun _ h => h.layoutN) ops init s h hwf hred

/-- `if slot a = 0 then t else e`. -/
theorem ifZero_wp (a : Nat) (t e : LCode) (s : State) (h : Inv s) (ha : a < nSlots) (Q : State → Prop)
    (ht : sv s a = 0 → ∀ q, Inv q → Eff [] s q → RegsExcept [10, 9] s q → WP isa t q Q)
    (he : sv s a ≠ 0 → ∀ q, Inv q → Eff [] s q → RegsExcept [10, 9] s q → WP isa e q Q) :
    WP isa (ifZero a t e) s Q := by
  obtain ⟨q, hq, hz, hr, hcf, hm, hrd, hwr, hl⟩ := orSlot_sv a s h ha
  have e13 : q.1.r 13 = s.r 13 := hr 13 (by decide)
  have e14 : q.1.r 14 = s.r 14 := hr 14 (by decide)
  have hE := eff_of_mem e13 e14 hm hrd hwr hl
  apply WP.seq
  refine WP.block_intro q hq ?_
  have hI := h.frm hE.frm
  apply WP.ite (q.1.r 10 == 0) (by simp [isa, eval, hcf])
  · intro hb
    exact ht (hz.mp (by simpa using hb)) q.1 hI hE hr
  · intro hb
    exact he (fun h0 => by simp [hz.mpr h0] at hb) q.1 hI hE hr

/-- A block given by an execution lemma. -/
theorem block_wp {is : List Instr} {s : State} {Q : State → Prop} {P : State × List Leak → Prop}
    (h : ∃ q, execBlock isa is s = some q ∧ P q) (hq : ∀ q, P q → Q q.1) : WP isa (.block is) s Q := by
  obtain ⟨q, h1, h2⟩ := h
  exact WP.block_intro q h1 (hq _ h2)

theorem exec_app {l₁ l₂ : List Instr} {s : State} {q₁ q₂ : State × List Leak}
    (h₁ : execBlock isa l₁ s = some q₁) (h₂ : execBlock isa l₂ q₁.1 = some q₂) :
    ∃ q, execBlock isa (l₁ ++ l₂) s = some q ∧ q.1 = q₂.1 :=
  ⟨(q₂.1, q₁.2 ++ q₂.2), by rw [execBlock_append, h₁]; simp [h₂], rfl⟩

/-- The decoded value of a reduced slot is zero iff the slot is. -/
theorem decode_eq_zero_iff (N x : Nat) (hc : Nat.Coprime (2 ^ 384) N) (hx : x < N) :
    decode N x = 0 ↔ x = 0 := by
  unfold decode
  have hu := ZMod.coe_mul_inv_eq_one _ hc
  constructor
  · intro h0
    have : (x : ZMod N) = 0 := by
      calc (x : ZMod N) = (x : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ * ((2 ^ 384 : ℕ) : ZMod N) := by
            rw [mul_assoc, mul_comm _ ((2 ^ 384 : ℕ) : ZMod N), hu, mul_one]
        _ = 0 := by rw [h0, zero_mul]
    rw [ZMod.natCast_eq_zero_iff] at this
    exact Nat.eq_zero_of_dvd_of_lt this hx
  · rintro rfl; simp

theorem decode_p_eq_zero_iff (x : Nat) (hx : x < p) : decode p x = 0 ↔ x = 0 :=
  decode_eq_zero_iff p x (coprime_two_pow_p 384) hx

theorem decode_n_eq_zero_iff (x : Nat) (hx : x < n) : decode n x = 0 ↔ x = 0 :=
  decode_eq_zero_iff n x (coprime_two_pow_n 384) hx

end CC.P384
