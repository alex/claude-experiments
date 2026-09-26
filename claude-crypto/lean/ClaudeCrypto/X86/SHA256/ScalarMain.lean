import ClaudeCrypto.X86.SHA256.ScalarBlock

/-!
# Correctness of `cc_sha256_blocks_x86_scalar`

The main theorem, `correct`, states that running the function body from any
state satisfying the calling convention and the function's preconditions

* terminates without faulting — in particular it only reads the message and the
  hash value (plus its own stack frame) and only writes the hash value and its
  own stack frame (memory safety);
* leaves `FIPS 180-4`'s `hashBlocks H msg` in the hash-value buffer;
* restores the stack pointer and all callee-saved registers; and
* leaves all memory outside the writable regions unchanged.
-/

namespace CC.X86.SHA256Scalar

open CC.Spec.SHA256

theorem loop_ok (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (s : State) (hn0 : 0 < g.n)
    (h : LoopInv g m1 0 s) : WP isa (.loop (.block blockCode) .ne) s (LoopInv g m1 g.n) := by
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => 0 < m ∧ m ≤ g.n ∧ LoopInv g m1 (g.n - m) s) ?_ g.n s
    ⟨hn0, le_refl _, by simpa using h⟩
  rintro m s ⟨hm0, hmn, hinv⟩
  refine WP.mono (block_ok g hwf m1 hmsg (g.n - m) (by omega) s hinv) ?_
  rintro s' ⟨hinv', hzf⟩
  have e : g.n - (g.n - m + 1) = m - 1 := by omega
  rw [e] at hzf
  have hm : m - 1 < 2 ^ 64 := by have := hwf.hn; omega
  by_cases hm1 : m = 1
  · subst hm1
    left
    refine ⟨by simp [isa, evalCond, hzf], ?_⟩
    have : g.n - 1 + 1 = g.n := by omega
    rwa [this] at hinv'
  · right
    refine ⟨?_, m - 1, by omega, by omega, by omega, ?_⟩
    · simp only [isa, evalCond, hzf, Option.map_some]
      congr 1
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp [Nat.mod_eq_of_lt hm] at this
      omega
    · have : g.n - m + 1 = g.n - (m - 1) := by omega
      rwa [this] at hinv'

theorem hashBlocks_eq (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    hashBlocks H msg = stateAfter H msg n := blocks_foldl H msg n hl

theorem stateAfter_zero (H : List Word) (msg : List (BitVec 8)) : stateAfter H msg 0 = H := rfl

theorem not_contains_mono (sp a : Addr) (n m : Nat) (h : n ≤ m) :
    ¬ (Region.mk sp m).Contains a 1 → ¬ (Region.mk sp n).Contains a 1 := by
  unfold Region.Contains; simp only; omega

/-- The state just before the epilogue. -/
structure PreEpi (s0 : State) (H : List Word) (msg : List (BitVec 8)) (st sp : Addr) (s : State) : Prop where
  rsp : s.gpr.rsp = sp
  h15 : s.mem.readW (sp + 64#64) 64 = s0.gpr.r15
  h14 : s.mem.readW (sp + 72#64) 64 = s0.gpr.r14
  h13 : s.mem.readW (sp + 80#64) 64 = s0.gpr.r13
  h12 : s.mem.readW (sp + 88#64) 64 = s0.gpr.r12
  hbp : s.mem.readW (sp + 96#64) 64 = s0.gpr.rbp
  hbx : s.mem.readW (sp + 104#64) 64 = s0.gpr.rbx
  hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!
  agree : Mem.AgreeL s0.mem s.mem s0.wr
  wr : s.wr = s0.wr

set_option maxHeartbeats 2000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_sha256_blocks_x86_scalar`.** -/
theorem correct (s : State) (H : List Word) (msg : List (BitVec 8)) (n : Nat) (st inp sp : Addr)
    (hH : H.length = 8) (hlen : msg.length = 64 * n) (hn : 64 * n + 64 < 2 ^ 64)
    (hrsp : s.gpr.rsp = sp + 112#64) (hrdi : s.gpr.rdi = st) (hrsi : s.gpr.rsi = inp)
    (hrdx : s.gpr.rdx = BitVec.ofNat 64 n)
    (hHmem : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (hmsg : ∀ i < 64 * n, s.mem (inp + BitVec.ofNat 64 i) = msg[i]!)
    (hrd : s.rd = [⟨inp, 64 * n⟩]) (hwr : s.wr = [⟨sp, 112⟩, ⟨st, 32⟩])
    (hsep1 : Mem.Sep sp 112 st 32) (hsep2 : Mem.Sep sp 112 inp (64 * n))
    (hsep3 : Mem.Sep st 32 inp (64 * n)) :
    WP isa code s fun s' =>
      (∀ k < 8, s'.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!) ∧
      s'.gpr.rsp = s.gpr.rsp ∧ s'.gpr.rbx = s.gpr.rbx ∧ s'.gpr.rbp = s.gpr.rbp ∧
      s'.gpr.r12 = s.gpr.r12 ∧ s'.gpr.r13 = s.gpr.r13 ∧ s'.gpr.r14 = s.gpr.r14 ∧
      s'.gpr.r15 = s.gpr.r15 ∧ Mem.AgreeL s.mem s'.mem s.wr := by
  -- the ghost state
  let g : Ghost := ⟨H, msg, n, st, inp, sp, s.rd, s.wr⟩
  have hwf : g.WF := ⟨hH, hlen, hn, hwr, hrd, hsep1, hsep2, hsep3⟩
  -- prologue
  obtain ⟨q1, hq1, hg1, sbx, sbp, s12, s13, s14, s15, hag1, hzf1, hrd1, hwr1⟩ :=
    prologue_exec s sp [⟨st, 32⟩] hrsp hwr
  apply WP.seq
  refine WP.block_intro q1 hq1 ?_
  apply WP.seq
  -- facts about memory after the prologue
  have hH1 : ∀ k < 8, q1.1.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]! := by
    intro k hk
    rw [hag1.readW _ _ (by simpa using hsep1.mono 0 (4 * k) 112 4 (by omega) (by omega) (by omega) (by omega)),
      hHmem k hk]
  have hmsg1 : ∀ i < 64 * n, q1.1.mem (inp + BitVec.ofNat 64 i) = msg[i]! := by
    intro i hi
    rw [hag1.apply _ (by simpa using hsep2.mono 0 i 112 1 (by omega) (by omega) (by omega) (by omega)),
      hmsg i hi]
  have hag1' : Mem.AgreeL s.mem q1.1.mem s.wr := Mem.AgreeL.of_agree _ hag1 (by simp [hwr])
  -- the saved registers survive anything that only writes the schedule buffer and the hash value
  have saved : ∀ (m : Mem), Mem.AgreeL q1.1.mem m [⟨sp, 64⟩, ⟨st, 32⟩] → ∀ k < 6,
      m.readW (sp + BitVec.ofNat 64 (64 + 8 * k)) 64 = q1.1.mem.readW (sp + BitVec.ofNat 64 (64 + 8 * k)) 64 := by
    intro m hm k hk
    apply hm.readW
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · show Mem.Sep sp 64 _ 8
      rw [sep_self_add]
      unfold Mem.Sep
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have : (0 : BitVec 64).toNat = 0 := rfl
      omega
    · simpa using (hsep1.symm.mono 0 (64 + 8 * k) 32 8 (by omega) (by omega) (by omega) (by omega))
  refine WP.mono (Q := PreEpi s H msg st sp) ?_ ?_
  · -- the body
    refine WP.ite (BitVec.ofNat 64 n == 0) (by simp only [isa, evalCond, hzf1, hg1, hrdx]) ?_ ?_
    · -- n = 0: nothing to do
      intro hb
      have h0 : n = 0 := by
        have := congrArg BitVec.toNat (beq_iff_eq.mp hb)
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this; exact this
      subst h0
      have hrsp1 : q1.1.gpr.rsp = sp := by rw [hg1]
      apply WP.block_nil
      refine PreEpi.mk hrsp1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hag1' hwr1
      · exact s15
      · exact s14
      · exact s13
      · exact s12
      · exact sbp
      · exact sbx
      · intro k hk
        have : hashBlocks H msg = H := by
          rw [hashBlocks_eq H msg 0 hlen]; rfl
        rw [this]; exact hH1 k hk
    · -- n > 0: load the hash value and run the loop
      intro hb
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hb
        · exact h
      apply WP.seq
      obtain ⟨q2, hq2, hg2, hm2, hrd2, hwr2⟩ := loadState_exec q1.1 st H (by rw [hg1]; exact hrdi)
        (fun k hk => by
          rw [hwr1, hwr]
          exact (inRegions_append _ _ _ _).mpr (Or.inr ⟨⟨st, 32⟩, by simp,
            by rw [region_contains_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega⟩))
        hH1
      refine WP.block_intro q2 hq2 ?_
      have hinv : LoopInv g q2.1.mem 0 q2.1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Mem.AgreeL.refl _ _, hrd2.trans (hrd1.trans rfl),
          hwr2.trans (hwr1.trans rfl)⟩
        · intro k hk
          rw [hg2]
          interval_cases k <;> rfl
        · intro k hk; rw [hm2]; exact hH1 k hk
        · rw [hg2]; show q1.1.gpr.rsp = sp; rw [hg1]
        · rw [hg2]; show q1.1.gpr.rdi = st; rw [hg1]; exact hrdi
        · rw [hg2]; show q1.1.gpr.rsi = _; rw [hg1]; simpa using hrsi
        · rw [hg2]; show q1.1.gpr.rdx = _; rw [hg1]; simpa using hrdx
      refine WP.mono (loop_ok g hwf q2.1.mem (by rw [hm2]; exact hmsg1) q2.1 hn0 hinv) ?_
      intro s3 h3
      have sv := saved s3.mem (by rw [← hm2]; exact h3.agree)
      refine ⟨h3.rsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h3.wr⟩
      · have := sv 0 (by decide); simp at this; rw [this]; simpa using s15
      · have := sv 1 (by decide); simp at this; rw [this]; simpa using s14
      · have := sv 2 (by decide); simp at this; rw [this]; simpa using s13
      · have := sv 3 (by decide); simp at this; rw [this]; simpa using s12
      · have := sv 4 (by decide); simp at this; rw [this]; simpa using sbp
      · have := sv 5 (by decide); simp at this; rw [this]; simpa using sbx
      · intro k hk
        rw [h3.hmem k hk, hashBlocks_eq H msg n hlen]; rfl
      · refine hag1'.trans ?_
        rw [← hm2]
        refine h3.agree.mono ?_
        intro a ha r hr
        rw [hwr] at ha
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact not_contains_mono sp a 64 112 (by omega) (ha _ (by simp))
        · exact ha _ (by simp [g])
  · -- epilogue
    intro s3 h3
    obtain ⟨q4, hq4, hg4, hm4, -, -⟩ := epilogue_exec s3 sp [⟨st, 32⟩] h3.rsp (by rw [h3.wr, hwr])
      _ _ _ _ _ _ h3.h15 h3.h14 h3.h13 h3.h12 h3.hbp h3.hbx
    refine WP.block_intro q4 hq4 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm4]; exact h3.hH
    all_goals first
      | (rw [hg4]; try simp [hrsp])
      | (rw [hm4]; exact h3.agree)

end CC.X86.SHA256Scalar
