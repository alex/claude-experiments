import ClaudeCrypto.X86.SHA256.ShaNiBlock

/-!
# Correctness of `cc_sha256_blocks_x86_shani`

The main theorem, `correct`, states that running the function body from any
state satisfying the function's preconditions

* terminates without faulting — in particular it only reads the message, the
  hash value and the constant tables, and only writes the hash value (memory
  safety);
* leaves FIPS 180-4's `hashBlocks H msg` in the hash-value buffer;
* preserves the stack pointer and all callee-saved registers (it uses no
  stack); and
* leaves all memory outside the writable regions unchanged.
-/

namespace CC.X86.SHA256ShaNi

open BitVec CC.X86 CC.Spec.SHA256

theorem hashBlocks_eq (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    hashBlocks H msg = stateAfter H msg n := blocks_foldl H msg n hl

/-- The regions holding the constant tables. -/
def tableRegions (labels : String → Addr) : List Region :=
  dataTables.map fun tb => ⟨labels tb.1, tb.2.length⟩

theorem kTable_length : kTable.length = 256 := by decide +kernel
theorem bswapMask_length : bswapMask.length = 16 := by decide

theorem mem_tables : (kLabel, kTable) ∈ dataTables ∧ (bswapLabel, bswapMask) ∈ dataTables := by
  simp [dataTables]

/-- A 128-bit little-endian load is four 32-bit little-endian loads. -/
theorem readW_128 (m : Mem) (a : Addr) :
    m.readW a 128 =
      vec4 (m.readW a 32) (m.readW (a + 4#64) 32) (m.readW (a + 8#64) 32) (m.readW (a + 12#64) 32) := by
  have h : ∀ k, k < 4 → m.readW (a + BitVec.ofNat 64 (4 * k)) 32 = (m.readW a 128).extractLsb' (32 * k) 32 := by
    intro k hk
    simp only [Mem.readW]
    rw [Mem.read_sub m a 16 (4 * k) 4 (by omega) (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    simp only [show i < 8 * 4 by omega, decide_true, Bool.true_and, show 32 * k + i < 128 by omega]
    congr 1; omega
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
  rw [h0, h1, h2, h3, vec4_ext]

/-- Reading back one word of a 128-bit store. -/
theorem readW_writeW_vec4 (m : Mem) (a : Addr) (x0 x1 x2 x3 : Word) (k : Nat) (hk : k < 4) :
    (m.writeW a (vec4 x0 x1 x2 x3)).readW (a + BitVec.ofNat 64 (4 * k)) 32 =
      (vec4 x0 x1 x2 x3).extractLsb' (32 * k) 32 := by
  simp only [Mem.readW, Mem.writeW]
  rw [Mem.read_write_within _ _ _ _ _ _ (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, show i < 8 * 4 by omega]
  simp only [show 8 * (4 * k) + i < 8 * (128 / 8) by omega, decide_true, Bool.true_and,
    show 32 * k + i < 128 by omega]
  congr 1; omega

/-- Reading back word `k` of the 32-byte hash value written by the two stores. -/
theorem read_state (m : Mem) (st : Addr) (a0 a1 a2 a3 e0 e1 e2 e3 : Word) (k : Nat) (hk : k < 8) :
    ((m.writeW st (vec4 a0 a1 a2 a3)).writeW (st + 16#64) (vec4 e0 e1 e2 e3)).readW
        (st + BitVec.ofNat 64 (4 * k)) 32 = [a0, a1, a2, a3, e0, e1, e2, e3][k]! := by
  by_cases h4 : k < 4
  · rw [Mem.readW_writeW_sep _ _ _ _ _ (by
      rw [show st + 16#64 = st + BitVec.ofNat 64 16 from rfl, sep_add_add]
      unfold Mem.Sep
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      interval_cases k <;> decide)]
    rw [readW_writeW_vec4 _ _ _ _ _ _ _ h4]
    interval_cases k <;> simp [vec4_ex0, vec4_ex32, vec4_ex64, vec4_ex96]
  · have e : st + BitVec.ofNat 64 (4 * k) = st + 16#64 + BitVec.ofNat 64 (4 * (k - 4)) := by
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; congr 2; omega
    rw [e, readW_writeW_vec4 _ _ _ _ _ _ _ (by omega)]
    interval_cases k <;> simp [vec4_ex0, vec4_ex32, vec4_ex64, vec4_ex96]

set_option maxHeartbeats 2000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_sha256_blocks_x86_shani`.**

`s` is the machine state on entry: `rdi` points to the hash value `H`
(eight 32-bit words, native byte order), `rsi` to the message `msg`
(`64 * n` bytes), and `rdx = n`; the program's constant tables are at their
labels.  The code may read the message and the tables and read and write the
hash value (`s.rd`, `s.wr` may contain further regions). -/
theorem correct (s : State) (H : List Word) (msg : List (BitVec 8)) (n : Nat) (st inp : Addr)
    (hlen : msg.length = 64 * n) (hn : 64 * n < 2 ^ 64)
    (hrdi : s.gpr.rdi = st) (hrsi : s.gpr.rsi = inp) (hrdx : s.gpr.rdx = BitVec.ofNat 64 n)
    (hHmem : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (hmsg : ∀ i < 64 * n, s.mem (inp + BitVec.ofNat 64 i) = msg[i]!)
    (htab : ∀ tb ∈ dataTables, ∀ j < tb.2.length, s.mem (s.labels tb.1 + BitVec.ofNat 64 j) = tb.2[j]!)
    (hrdm : ⟨inp, 64 * n⟩ ∈ s.rd) (hrdt : ∀ r ∈ tableRegions s.labels, r ∈ s.rd)
    (hwr : ⟨st, 32⟩ ∈ s.wr) :
    WP isa code s fun s' =>
      (∀ k < 8, s'.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!) ∧
      s'.gpr.rsp = s.gpr.rsp ∧ s'.gpr.rbx = s.gpr.rbx ∧ s'.gpr.rbp = s.gpr.rbp ∧
      s'.gpr.r12 = s.gpr.r12 ∧ s'.gpr.r13 = s.gpr.r13 ∧ s'.gpr.r14 = s.gpr.r14 ∧
      s'.gpr.r15 = s.gpr.r15 ∧ Mem.AgreeL s.mem s'.mem s.wr := by
  let G : Ghost := ⟨H, msg, n, s⟩
  have hinp : G.inp = inp := hrsi
  have hwf : G.WF := by
    refine ⟨hlen, hn, by rw [hinp]; exact hmsg, fun j hj => ?_, fun j hj => ?_, by rw [hinp]; exact hrdm,
      hrdt _ ?_, hrdt _ ?_⟩
    · exact htab _ mem_tables.1 j (by rw [kTable_length]; exact hj)
    · exact htab _ mem_tables.2 j (by rw [bswapMask_length]; exact hj)
    · simp only [tableRegions, List.mem_map]; exact ⟨_, mem_tables.1, by rw [kTable_length]; rfl⟩
    · simp only [tableRegions, List.mem_map]; exact ⟨_, mem_tables.2, by rw [bswapMask_length]; rfl⟩
  have hwrst : ∀ k, k + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 k) 16 := fun k hk =>
    ⟨_, List.mem_append_right _ hwr, Region.contains_offset _ _ _ _ hk (by norm_num)⟩
  -- the entry test
  obtain ⟨q0, hq0, hz0, hg0, -, hm0, hrd0, hwr0, hl0⟩ := entry_exec s
  apply WP.seq
  refine WP.block_intro q0 hq0 ?_
  refine WP.ite (s.gpr.rdx == 0#64) (by simp only [isa, evalCond, hz0]) ?_ ?_
  · -- n = 0: nothing to do
    intro hb
    have h0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hb)
      simp only [hrdx, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this; simpa using this
    subst h0
    refine WP.block_nil ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0, hashBlocks_eq H msg 0 hlen]; exact hHmem k hk
    all_goals first | (rw [hg0]) | (rw [hm0]; exact Mem.AgreeL.refl _ _)
  · -- n > 0: load the hash value, run the loop, store the hash value
    intro hb
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [hrdx] at hb
      · exact h
    apply WP.seq
    have hp0 := hwrst 0 (by decide)
    have hp1 := hwrst 16 (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hp0 hp1
    have hpb : InRegions (q0.1.rd ++ q0.1.wr) (q0.1.labels bswapLabel) 16 := by
      rw [hrd0, hwr0, hl0]
      have := inRegions_of_mem (rs' := s.wr) hwf.hrdB (by norm_num) 0 16 (by simp)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      exact this
    obtain ⟨q1, hq1, ey1, ey2, ey8, eg1, em1, erd1, ewr1, el1⟩ := loadState_exec q0.1
      (by rw [hrd0, hwr0, hg0, hrdi]; exact hp0) (by rw [hrd0, hwr0, hg0, hrdi]; exact hp1) hpb
    refine WP.block_intro q1 hq1 ?_
    -- the loop invariant holds initially
    have hH4 : ∀ k, k < 8 → s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]! := hHmem
    have hv0 : s.mem.readW st 128 = vec4 H[0]! H[1]! H[2]! H[3]! := by
      rw [readW_128]
      have h1 := hH4 1 (by decide); have h2 := hH4 2 (by decide); have h3 := hH4 3 (by decide)
      have h0 := hH4 0 (by decide)
      simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
      rw [h0, h1, h2, h3]
    have hv1 : s.mem.readW (st + 16#64) 128 = vec4 H[4]! H[5]! H[6]! H[7]! := by
      rw [readW_128]
      have e : ∀ c, st + 16#64 + BitVec.ofNat 64 c = st + BitVec.ofNat 64 (16 + c) := fun c => by
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
      have e4 := e 4; have e8 := e 8; have e12 := e 12
      simp only [Nat.reduceAdd] at e4 e8 e12
      rw [e4, e8, e12]
      have h4 := hH4 4 (by decide); have h5 := hH4 5 (by decide); have h6 := hH4 6 (by decide)
      have h7 := hH4 7 (by decide)
      simp only [Nat.reduceMul] at h4 h5 h6 h7
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, h4, h5, h6, h7]
    have hinv : LoopInv G 0 q1.1 := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [em1, hm0]
      · rw [erd1, hrd0]
      · rw [ewr1, hwr0]
      · rw [el1, hl0]
      · intro r _ _; rw [eg1, hg0]
      · rw [ey1, hg0, hrdi, hm0, hv0, hv1, pshufd_27, pshufd_27, punpckh_vec4]; rfl
      · rw [ey2, hg0, hrdi, hm0, hv0, hv1, pshufd_27, pshufd_27, punpckl_vec4]; rfl
      · rw [ey8, hm0, hl0]; exact bswap_vec G hwf
      · rw [eg1, hg0, hrsi]; simp [G, Ghost.inp, hrsi]
      · rw [eg1, hg0, hrdx]; rfl
    apply WP.seq
    refine WP.mono (loop_ok G hwf _ hn0 hinv) ?_
    intro s3 h3
    -- the final store
    have hrdi3 : s3.gpr.rdi = st := (h3.frame.gpr .rdi (by decide) (by decide)).trans hrdi
    have hwr3 : s3.wr = s.wr := h3.frame.wr
    have hq0 : InRegions s3.wr (s3.gpr.rdi) 16 := by
      rw [hwr3, hrdi3]
      exact ⟨_, hwr, by rw [region_contains_self]; decide⟩
    have hq1 : InRegions s3.wr (s3.gpr.rdi + 16#64) 16 := by
      rw [hwr3, hrdi3]
      exact ⟨_, hwr, Region.contains_offset _ _ 16 16 (by decide) (by norm_num)⟩
    obtain ⟨q4, hq4, em4, eg4, -, -⟩ := storeState_exec s3 hq0 hq1
    refine WP.block_intro q4 hq4 ?_
    have hy1 := h3.y1; have hy2 := h3.y2
    have hmem : q4.1.mem = (s3.mem.writeW st (vec4 (initVars (G.Hb n)).a (initVars (G.Hb n)).b
        (initVars (G.Hb n)).c (initVars (G.Hb n)).d)).writeW (st + 16#64)
        (vec4 (initVars (G.Hb n)).e (initVars (G.Hb n)).f (initVars (G.Hb n)).g (initVars (G.Hb n)).h) := by
      rw [em4, hrdi3, hy1, hy2, abef, cdgh, punpckh_vec4, punpckl_vec4, pshufd_27, pshufd_27]
    have gp : ∀ r : Reg, r ≠ .rsi → r ≠ .rdx → q4.1.gpr.get r = s.gpr.get r := fun r h1 h2 => by
      rw [eg4]; exact h3.frame.gpr r h1 h2
    refine ⟨fun k hk => ?_, gp .rsp (by decide) (by decide), gp .rbx (by decide) (by decide),
      gp .rbp (by decide) (by decide), gp .r12 (by decide) (by decide), gp .r13 (by decide) (by decide),
      gp .r14 (by decide) (by decide), gp .r15 (by decide) (by decide), ?_⟩
    · rw [hmem, read_state _ _ _ _ _ _ _ _ _ _ _ hk, hashBlocks_eq H msg n hlen]
      simp only [initVars]
      interval_cases k <;> rfl
    · rw [hmem, h3.frame.mem]
      refine (Mem.AgreeL.writeW (Mem.AgreeL.refl _ _) _ hwr _ _ ?_).writeW _ hwr _ _ ?_
      · rw [region_contains_self]; decide
      · exact Region.contains_offset _ _ 16 16 (by decide) (by norm_num)

end CC.X86.SHA256ShaNi
