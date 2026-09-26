import ClaudeCrypto.X86.SHA256.Avx2Iter

/-!
# Correctness of `cc_sha256_blocks_x86_avx2`

The main theorem, `correct`, states that running the function body from any
state satisfying the calling convention and the function's preconditions

* terminates without faulting — in particular it only reads the message, the
  hash value, the constant tables and its own stack frame, and only writes the
  hash value and its own stack frame (memory safety);
* leaves FIPS 180-4's `hashBlocks H msg` in the hash-value buffer;
* restores the stack pointer and all callee-saved registers; and
* leaves all memory outside the writable regions unchanged.
-/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

theorem loop_ok (g : Ghost) (hwf : g.WF) (m1 : Mem) (hm1 : g.MemFacts m1) (s : State) (hn0 : 0 < g.n)
    (h : LoopInv g m1 0 s) : WP isa (.loop body .ne) s (LoopInv g m1 g.n) := by
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => 0 < m ∧ m ≤ g.n ∧ LoopInv g m1 (g.n - m) s) ?_ g.n s
    ⟨hn0, le_refl _, by simpa using h⟩
  rintro m s ⟨hm0, hmn, hinv⟩
  refine WP.mono (body_ok g hwf m1 hm1 (g.n - m) (by omega) s hinv) ?_
  rintro s' ⟨k', hk1, hk2, hinv', hzf⟩
  have hn := hwf.hn
  by_cases hkn : k' = g.n
  · subst hkn
    left
    refine ⟨by simp [isa, evalCond, hzf], hinv'⟩
  · right
    refine ⟨?_, g.n - k', by omega, by omega, by omega, ?_⟩
    · simp only [isa, evalCond, hzf, Option.map_some]
      congr 1
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp [Nat.mod_eq_of_lt (show g.n - k' < 2 ^ 64 by omega)] at this
      omega
    · rwa [show g.n - (g.n - k') = k' by omega]

theorem hashBlocks_eq (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    hashBlocks H msg = stateAfter H msg n := blocks_foldl H msg n hl

/-- The state just before the epilogue. -/
structure PreEpi (s0 : State) (H : List Word) (msg : List (BitVec 8)) (st sp : Addr) (s : State) : Prop where
  rsp : s.gpr.rsp = sp
  h15 : s.mem.readW (sp + 512#64) 64 = s0.gpr.r15
  h14 : s.mem.readW (sp + 520#64) 64 = s0.gpr.r14
  h13 : s.mem.readW (sp + 528#64) 64 = s0.gpr.r13
  h12 : s.mem.readW (sp + 536#64) 64 = s0.gpr.r12
  hbp : s.mem.readW (sp + 544#64) 64 = s0.gpr.rbp
  hbx : s.mem.readW (sp + 552#64) 64 = s0.gpr.rbx
  hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!
  agree : Mem.AgreeL s0.mem s.mem s0.wr
  wr : s.wr = s0.wr

theorem not_contains_mono (sp a : Addr) (n m : Nat) (h : n ≤ m) :
    ¬ (Region.mk sp m).Contains a 1 → ¬ (Region.mk sp n).Contains a 1 := by
  unfold Region.Contains; simp only; omega

set_option maxHeartbeats 4000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_sha256_blocks_x86_avx2`.** -/
theorem correct (s : State) (H : List Word) (msg : List (BitVec 8)) (n : Nat) (st inp sp : Addr)
    (hH : H.length = 8) (hlen : msg.length = 64 * n) (hn : 64 * n + 128 < 2 ^ 64)
    (hrsp : s.gpr.rsp = sp + 560#64) (hrdi : s.gpr.rdi = st) (hrsi : s.gpr.rsi = inp)
    (hrdx : s.gpr.rdx = BitVec.ofNat 64 n)
    (hHmem : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (hmsg : ∀ i < 64 * n, s.mem (inp + BitVec.ofNat 64 i) = msg[i]!)
    (htab : ∀ tb ∈ dataTables, ∀ j < tb.2.length, s.mem (s.labels tb.1 + BitVec.ofNat 64 j) = tb.2[j]!)
    (hrd : s.rd = ⟨inp, 64 * n⟩ :: tableRegions s.labels) (hwr : s.wr = [⟨sp, 560⟩, ⟨st, 32⟩])
    (hsep1 : Mem.Sep sp 560 st 32) (hsep2 : Mem.Sep sp 560 inp (64 * n))
    (hsep3 : Mem.Sep st 32 inp (64 * n))
    (hsep4 : ∀ tb ∈ dataTables, Mem.Sep sp 560 (s.labels tb.1) tb.2.length)
    (hsep5 : ∀ tb ∈ dataTables, Mem.Sep st 32 (s.labels tb.1) tb.2.length) :
    WP isa code s fun s' =>
      (∀ k < 8, s'.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!) ∧
      s'.gpr.rsp = s.gpr.rsp ∧ s'.gpr.rbx = s.gpr.rbx ∧ s'.gpr.rbp = s.gpr.rbp ∧
      s'.gpr.r12 = s.gpr.r12 ∧ s'.gpr.r13 = s.gpr.r13 ∧ s'.gpr.r14 = s.gpr.r14 ∧
      s'.gpr.r15 = s.gpr.r15 ∧ Mem.AgreeL s.mem s'.mem s.wr := by
  let g : Ghost := ⟨H, msg, n, st, inp, sp, s.labels⟩
  have hwf : g.WF := ⟨hH, hlen, hn, hsep1, hsep2, hsep3, hsep4, hsep5⟩
  -- prologue
  obtain ⟨q1, hq1, hg1, sbx, sbp, s12, s13, s14, s15, hag1, hzf1, hv1, hrd1, hwr1, hl1⟩ :=
    prologue_exec s sp [⟨st, 32⟩] hrsp hwr
  apply WP.seq
  refine WP.block_intro q1 hq1 ?_
  apply WP.seq
  have hH1 : ∀ k < 8, q1.1.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]! := by
    intro k hk
    rw [hag1.readW _ _ (by simpa using hsep1.mono 0 (4 * k) 560 4 (by omega) (by omega) (by omega) (by omega)),
      hHmem k hk]
  have hm1 : g.MemFacts q1.1.mem := by
    refine ⟨fun i hi => ?_, fun tb htb j hj => ?_⟩
    · have hi' : i < 64 * n := hi
      rw [hag1.apply _ (by simpa using hsep2.mono 0 i 560 1 (by omega) (by omega) (by omega) (by omega)),
        hmsg i hi]
    · rw [hag1.apply _ (by simpa using (hsep4 tb htb).mono 0 j 560 1 (by omega) (by omega) (by omega) (by omega)),
        htab tb htb j hj]
  have hag1' : Mem.AgreeL s.mem q1.1.mem s.wr := Mem.AgreeL.of_agree _ hag1 (by simp [hwr])
  -- the saved registers survive anything that only writes the schedule buffer and the hash value
  have saved : ∀ (m : Mem), Mem.AgreeL q1.1.mem m [⟨sp, 512⟩, ⟨st, 32⟩] → ∀ k < 6,
      m.readW (sp + BitVec.ofNat 64 (512 + 8 * k)) 64 = q1.1.mem.readW (sp + BitVec.ofNat 64 (512 + 8 * k)) 64 := by
    intro m hm k hk
    apply hm.readW
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · show Mem.Sep sp 512 _ 8
      rw [sep_self_add]
      unfold Mem.Sep
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have : (0 : BitVec 64).toNat = 0 := rfl
      omega
    · simpa using (hsep1.symm.mono 0 (512 + 8 * k) 32 8 (by omega) (by omega) (by omega) (by omega))
  refine WP.mono (Q := PreEpi s H msg st sp) ?_ ?_
  · refine WP.ite (BitVec.ofNat 64 n == 0) (by simp only [isa, evalCond, hzf1, hg1, hrdx]) ?_ ?_
    · -- n = 0: nothing to do
      intro hb
      have h0 : n = 0 := by
        have := congrArg BitVec.toNat (beq_iff_eq.mp hb)
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this; exact this
      subst h0
      apply WP.block_nil
      refine ⟨by rw [hg1], s15, s14, s13, s12, sbp, sbx, ?_, hag1', hwr1⟩
      intro k hk
      have : hashBlocks H msg = H := by rw [hashBlocks_eq H msg 0 hlen]; rfl
      rw [this]; exact hH1 k hk
    · intro hb
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hb
        · exact h
      apply WP.seq
      have hmasks := masks_of hm1
      have tperm : ∀ l bytes, (l, bytes) ∈ dataTables → 32 ≤ bytes.length →
          InRegions (q1.1.rd ++ q1.1.wr) (q1.1.labels l) 32 := by
        intro l bytes hl hlen'
        rw [inRegions_append, hrd1, hrd, hl1]; left
        refine ⟨⟨s.labels l, bytes.length⟩, ?_, ?_⟩
        · simp only [List.mem_cons, tableRegions, List.mem_map]; right; exact ⟨_, hl, rfl⟩
        · unfold Region.Contains; simp; omega
      obtain ⟨q2, hq2, hg2, hy12, hy10, hy11, hm2, hrd2, hwr2, hl2⟩ := setup_exec q1.1 st H
        (by rw [hg1]; exact hrdi)
        (fun k hk => by
          rw [hwr1, hwr]
          exact (inRegions_append _ _ _ _).mpr (Or.inr ⟨⟨st, 32⟩, by simp,
            by rw [region_contains_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega⟩))
        hH1 (tperm _ _ mem_tables.2.1 (by decide)) (tperm _ _ mem_tables.2.2.1 (by decide))
        (tperm _ _ mem_tables.2.2.2 (by decide))
      refine WP.block_intro q2 hq2 ?_
      have hinv : LoopInv g q1.1.mem 0 q2.1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm2]; exact Mem.AgreeL.refl _ _, ?_, ?_, ?_⟩
        · intro k hk; rw [hg2]; interval_cases k <;> rfl
        · intro k hk; rw [hm2]; exact hH1 k hk
        · rw [hg2]; show q1.1.gpr.rsp = sp; rw [hg1]
        · rw [hg2]; show q1.1.gpr.rdi = st; rw [hg1]; exact hrdi
        · rw [hg2]; show q1.1.gpr.rsi = _; rw [hg1]; simpa using hrsi
        · rw [hg2]; show q1.1.gpr.rdx = _; rw [hg1]; simpa using hrdx
        · rw [hy10, hl1]; exact hmasks.2.1
        · rw [hy11, hl1]; exact hmasks.2.2
        · rw [hy12, hl1]; exact hmasks.1
        · rw [hrd2, hrd1, hrd]; rfl
        · rw [hwr2, hwr1, hwr]; rfl
        · rw [hl2, hl1]
      refine WP.mono (loop_ok g hwf q1.1.mem hm1 q2.1 hn0 hinv) ?_
      intro s3 h3
      have sv := saved s3.mem h3.agree
      refine ⟨h3.rsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := sv 0 (by decide); simp at this; rw [this]; simpa using s15
      · have := sv 1 (by decide); simp at this; rw [this]; simpa using s14
      · have := sv 2 (by decide); simp at this; rw [this]; simpa using s13
      · have := sv 3 (by decide); simp at this; rw [this]; simpa using s12
      · have := sv 4 (by decide); simp at this; rw [this]; simpa using sbp
      · have := sv 5 (by decide); simp at this; rw [this]; simpa using sbx
      · intro k hk
        rw [h3.hmem k hk, hashBlocks_eq H msg n hlen]; rfl
      · refine hag1'.trans ?_
        refine h3.agree.mono ?_
        intro a ha r hr
        rw [hwr] at ha
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact not_contains_mono sp a 512 560 (by omega) (ha _ (by simp))
        · exact ha _ (by simp [g])
      · rw [h3.wr, hwr]; rfl
  · -- epilogue
    intro s3 h3
    obtain ⟨q4, hq4, hg4, hm4, -, -⟩ := epilogue_exec s3 sp [⟨st, 32⟩] h3.rsp (by rw [h3.wr, hwr])
      _ _ _ _ _ _ h3.h15 h3.h14 h3.h13 h3.h12 h3.hbp h3.hbx
    refine WP.block_intro q4 hq4 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm4]; exact h3.hH
    all_goals first
      | (rw [hg4]; try simp [hrsp])
      | (rw [hm4]; exact h3.agree)

end CC.X86.SHA256Avx2
