import ClaudeCrypto.X86.SHA256.Avx2Block
import ClaudeCrypto.X86.SHA256.Avx2Small

/-! # AVX2 SHA-256: one loop iteration -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

set_option maxRecDepth 100000 in
theorem kTable_lanes : ∀ g < 16, ∀ i < 8,
    lane 32 (lanes 32 fun j => kTable[32 * g + j]!) i = K[4 * g + i % 4]! := by
  decide +kernel

theorem kTable_length : kTable.length = 512 := by decide +kernel

/-- The regions holding the constant tables. -/
def tableRegions (labels : String → Addr) : List Region :=
  dataTables.map fun tb => ⟨labels tb.1, tb.2.length⟩

/-- The parameters of a call. -/
structure Ghost where
  H : List Word
  msg : List (BitVec 8)
  n : Nat
  st : Addr
  inp : Addr
  sp : Addr
  labels : String → Addr

namespace Ghost

def Hb (g : Ghost) (k : Nat) : List Word := stateAfter g.H g.msg k
def Mb (g : Ghost) (k : Nat) : List Word := msgBlock g.msg k
def rd (g : Ghost) : List Region := ⟨g.inp, 64 * g.n⟩ :: tableRegions g.labels
def wr (g : Ghost) : List Region := [⟨g.sp, 560⟩, ⟨g.st, 32⟩]

/-- The preconditions on the parameters. -/
structure WF (g : Ghost) : Prop where
  hH : g.H.length = 8
  hlen : g.msg.length = 64 * g.n
  hn : 64 * g.n + 128 < 2 ^ 64
  sep_sp_st : Mem.Sep g.sp 560 g.st 32
  sep_sp_inp : Mem.Sep g.sp 560 g.inp (64 * g.n)
  sep_st_inp : Mem.Sep g.st 32 g.inp (64 * g.n)
  sep_sp_tab : ∀ tb ∈ dataTables, Mem.Sep g.sp 560 (g.labels tb.1) tb.2.length
  sep_st_tab : ∀ tb ∈ dataTables, Mem.Sep g.st 32 (g.labels tb.1) tb.2.length

/-- The read-only memory contents. -/
structure MemFacts (g : Ghost) (m : Mem) : Prop where
  msg : ∀ i < 64 * g.n, m (g.inp + BitVec.ofNat 64 i) = g.msg[i]!
  tab : ∀ tb ∈ dataTables, ∀ j < tb.2.length, m (g.labels tb.1 + BitVec.ofNat 64 j) = tb.2[j]!

end Ghost

theorem sep_shrink {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) (n' : Nat) (hn : n' ≤ n) (hn' : 0 < n')
    (hk : 0 < k) : Mem.Sep a n' b k := by
  simpa using h.mono 0 0 n' k (by omega) (by omega) hn' hk

theorem Ghost.MemFacts.agree {g : Ghost} (hwf : g.WF) {m1 m : Mem} (h : g.MemFacts m1)
    (hag : Mem.AgreeL m1 m [⟨g.sp, 512⟩, ⟨g.st, 32⟩]) : g.MemFacts m := by
  refine ⟨fun i hi => ?_, fun tb htb j hj => ?_⟩
  · rw [hag.apply _ ?_, h.msg i hi]
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact sep_sub (sep_shrink hwf.sep_sp_inp 512 (by omega) (by omega) (by omega)) i 1 (by omega)
        (by omega) (by omega)
    · exact sep_sub hwf.sep_st_inp i 1 (by omega) (by omega) (by omega)
  · rw [hag.apply _ ?_, h.tab tb htb j hj]
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact sep_sub (sep_shrink (hwf.sep_sp_tab tb htb) 512 (by omega) (by omega) (by omega)) j 1
        (by omega) (by omega) (by omega)
    · exact sep_sub (hwf.sep_st_tab tb htb) j 1 (by omega) (by omega) (by omega)

theorem mem_tables : (kLabel, kTable) ∈ dataTables ∧ (bswapLabel, bswapMask) ∈ dataTables ∧
    (s00BALabel, shuf00BA) ∈ dataTables ∧ (sDC00Label, shufDC00) ∈ dataTables := by
  simp [dataTables]

theorem readW_table {g : Ghost} {m : Mem} (h : g.MemFacts m) (l : String) (bytes : List (BitVec 8))
    (hl : (l, bytes) ∈ dataTables) (off : Nat) (hoff : off + 32 ≤ bytes.length) :
    m.readW (g.labels l + BitVec.ofNat 64 off) 256 = lanes 32 fun j => bytes[off + j]! := by
  apply readW_eq_lanes
  intro j hj
  rw [addr_add_ofNat]
  exact h.tab _ hl (off + j) (by show off + j < bytes.length; omega)

theorem masks_of {g : Ghost} {m : Mem} (h : g.MemFacts m) :
    m.readW (g.labels bswapLabel) 256 = maskV bswapMask ∧
    m.readW (g.labels s00BALabel) 256 = maskV shuf00BA ∧
    m.readW (g.labels sDC00Label) 256 = maskV shufDC00 := by
  have e : ∀ a : Addr, a = a + BitVec.ofNat 64 0 := fun a => by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e (g.labels _), readW_table h _ bswapMask mem_tables.2.1 0 (by decide)]; simp only [Nat.zero_add]; rfl
  · rw [e (g.labels _), readW_table h _ shuf00BA mem_tables.2.2.1 0 (by decide)]; simp only [Nat.zero_add]; rfl
  · rw [e (g.labels _), readW_table h _ shufDC00 mem_tables.2.2.2 0 (by decide)]; simp only [Nat.zero_add]; rfl

theorem kfacts_of {g : Ghost} (hwf : g.WF) (s : State) (h : g.MemFacts s.mem) (hrd : s.rd = g.rd)
    (hlab : s.labels = g.labels) : KFacts s g.sp := by
  refine ⟨fun j hj i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [kAddr, hlab, readW_table h _ _ mem_tables.1 (32 * j) (by rw [kTable_length]; omega)]
    exact kTable_lanes j hj i hi
  · rw [kAddr, hrd, hlab]
    refine ⟨⟨g.labels kLabel, 512⟩, ?_, Region.contains_offset _ _ _ _ (by omega) (by decide)⟩
    simp [Ghost.rd, tableRegions, dataTables, kTable_length]
  · rw [kAddr, hlab]
    have := hwf.sep_sp_tab _ mem_tables.1
    rw [kTable_length] at this
    exact sep_sub (sep_shrink this 512 (by omega) (by omega) (by omega)) (32 * j) 32 (by omega)
      (by omega) (by omega)

/-! ## The loop -/

/-- The invariant at the head of the loop, after `k` blocks. `m1` is the memory
after the prologue. -/
structure LoopInv (g : Ghost) (m1 : Mem) (k : Nat) (s : State) : Prop where
  regs : ∀ i < 8, s.gpr.get (hReg i) = ((g.Hb k)[i]!).setWidth 64
  hmem : ∀ i < 8, s.mem.readW (g.st + BitVec.ofNat 64 (4 * i)) 32 = (g.Hb k)[i]!
  rsp : s.gpr.rsp = g.sp
  rdi : s.gpr.rdi = g.st
  rsi : s.gpr.rsi = g.inp + BitVec.ofNat 64 (64 * k)
  rdx : s.gpr.rdx = BitVec.ofNat 64 (g.n - k)
  y10 : s.getV .y10 = maskV shuf00BA
  y11 : s.getV .y11 = maskV shufDC00
  y12 : s.getV .y12 = maskV bswapMask
  agree : Mem.AgreeL m1 s.mem [⟨g.sp, 512⟩, ⟨g.st, 32⟩]
  rd : s.rd = g.rd
  wr : s.wr = g.wr
  labels : s.labels = g.labels

/-- After the first block of an iteration (lane 0) and the second parity test. -/
structure Mid (g : Ghost) (m1 : Mem) (k blkB : Nat) (s : State) : Prop where
  regs : ∀ i < 8, s.gpr.get (hReg i) = ((g.Hb (k + 1))[i]!).setWidth 64
  hmem : ∀ i < 8, s.mem.readW (g.st + BitVec.ofNat 64 (4 * i)) 32 = (g.Hb (k + 1))[i]!
  rsp : s.gpr.rsp = g.sp
  rdi : s.gpr.rdi = g.st
  rsi : s.gpr.rsi = g.inp + BitVec.ofNat 64 (64 * k)
  rdx : s.gpr.rdx = BitVec.ofNat 64 (g.n - k)
  y10 : s.getV .y10 = maskV shuf00BA
  y11 : s.getV .y11 = maskV shufDC00
  y12 : s.getV .y12 = maskV bswapMask
  agree : Mem.AgreeL m1 s.mem [⟨g.sp, 512⟩, ⟨g.st, 32⟩]
  rd : s.rd = g.rd
  wr : s.wr = g.wr
  labels : s.labels = g.labels
  buf : BufInv (Wt (g.Mb k)) (Wt (g.Mb blkB)) s.mem g.sp 16
  zf : s.zf = some (decide ((g.n - k) % 2 = 0))

theorem Hb_succ (g : Ghost) (k : Nat) : compress (g.Hb k) (g.Mb k) = g.Hb (k + 1) := by
  rw [Ghost.Hb, Ghost.Hb, stateAfter_succ]; rfl

theorem agree_step {m1 m m' : Mem} {sp st : Addr} (h1 : Mem.AgreeL m1 m [⟨sp, 512⟩, ⟨st, 32⟩])
    (h2 : Mem.Agree m m' ⟨sp, 512⟩) : Mem.AgreeL m1 m' [⟨sp, 512⟩, ⟨st, 32⟩] :=
  h1.trans (Mem.AgreeL.of_agree _ h2 (by simp))

theorem mid_ok (g : Ghost) (hwf : g.WF) (m1 : Mem) (hm1 : g.MemFacts m1) (k blkB : Nat) (hk : k < g.n)
    (hB : blkB < g.n) (s sL : State) (h : LoopInv g m1 k s)
    (hL : ∀ j < 4, HoldsGroup (vpshufbV (sL.getV (ymm j)) (maskV bswapMask)) (Wt (g.Mb k)) (Wt (g.Mb blkB)) j)
    (hg : sL.gpr = s.gpr) (hm : sL.mem = s.mem) (h10 : sL.getV .y10 = s.getV .y10)
    (h11 : sL.getV .y11 = s.getV .y11) (h12 : sL.getV .y12 = s.getV .y12) (hrd : sL.rd = s.rd)
    (hwr : sL.wr = s.wr) (hlab : sL.labels = s.labels) :
    WP isa (.block (prep ++ lane0 ++ parity)) sL (Mid g m1 k blkB) := by
  have hms : g.MemFacts s.mem := hm1.agree hwf h.agree
  have hkf : KFacts sL g.sp := kfacts_of hwf sL (by rw [hm]; exact hms) (hrd.trans h.rd) (hlab.trans h.labels)
  have hsep : Mem.Sep g.sp 512 g.st 32 := sep_shrink hwf.sep_sp_st 512 (by omega) (by omega) (by omega)
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (prep_ok (Wt (g.Mb k)) (Wt (g.Mb blkB)) g.sp [⟨g.st, 32⟩] sL sL hkf hL (h12.trans h.y12)
    (by rw [hg, h.rsp]) (by rw [hwr, h.wr]; rfl) rfl rfl (Mem.Agree.refl _ _)) ?_
  intro s3 h3
  have ag3 : Mem.AgreeL m1 s3.mem [⟨g.sp, 512⟩, ⟨g.st, 32⟩] := agree_step h.agree (hm ▸ h3.mem)
  have hkf3 : KFacts s3 g.sp := kfacts_of hwf s3 (hm1.agree hwf ag3) (h3.rd.trans (hrd.trans h.rd))
    (h3.labels.trans (hlab.trans h.labels))
  have hM : (g.Mb k).length = 16 := msgBlock_length _ _
  refine WP.mono (lane0_ok (g.Hb k) (g.Mb k) hM (Wt (g.Mb blkB)) (Wt_recur _) g.sp g.st [] hsep s3 hkf3
    (by rw [h3.gpr, hg]; exact h.regs)
    (hmem_of_agree hsep (hm ▸ h3.mem) _ h.hmem) h3.done h3.buf
    (by rw [h3.y10, h10]; exact h.y10) (by rw [h3.y11, h11]; exact h.y11)
    (by rw [h3.gpr, hg]; exact h.rsp) (by rw [h3.gpr, hg]; exact h.rdi)
    (by rw [h3.wr, hwr, h.wr]; rfl)) ?_
  intro s4 ⟨h4, hb4⟩
  obtain ⟨q5, hq5, z5, g5, v5, m5, rd5, wr5, l5⟩ := parity_exec s4
  have gv5 : ∀ v, q5.1.getV v = s4.getV v := fun v => by simp only [State.getV, v5]
  refine WP.block_intro q5 hq5 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g5, ← Hb_succ]; exact h4.regs
  · rw [m5, ← Hb_succ]; exact h4.hmem
  · rw [g5, h4.rsp, h3.gpr, hg]; exact h.rsp
  · rw [g5, h4.rdi, h3.gpr, hg]; exact h.rdi
  · rw [g5, h4.rsi, h3.gpr, hg]; exact h.rsi
  · rw [g5, h4.rdx, h3.gpr, hg]; exact h.rdx
  · rw [gv5, h4.y10, h3.y10, h10]; exact h.y10
  · rw [gv5, h4.y11, h3.y11, h11]; exact h.y11
  · rw [gv5, h4.y12, h3.y12, h12]; exact h.y12
  · rw [m5]; exact ag3.trans h4.mem
  · rw [rd5, h4.rd, h3.rd, hrd]; exact h.rd
  · rw [wr5, h4.wr, h3.wr, hwr]; exact h.wr
  · rw [l5, h4.labels, h3.labels, hlab]; exact h.labels
  · rw [m5]; exact hb4
  · rw [z5, h4.rdx, h3.gpr, hg, h.rdx, parity_bit _ (by have := hwf.hn; omega)]

theorem ofNat_sub_ofNat (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem load_perm (g : Ghost) (s : State) (hrd : s.rd = g.rd) (k j : Nat) (hj : 64 * k + 16 * j + 16 ≤ 64 * g.n)
    (hn : 64 * g.n < 2 ^ 64) :
    InRegions (s.rd ++ s.wr) (g.inp + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 (16 * j)) 16 := by
  rw [inRegions_append, hrd, addr_add_ofNat]
  left
  exact ⟨_, List.mem_cons_self .., Region.contains_offset _ _ _ _ hj hn⟩

theorem ne_eval (s : State) (b : Bool) (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  simp only [isa, evalCond, h, Option.map_some]

theorem body_ok (g : Ghost) (hwf : g.WF) (m1 : Mem) (hm1 : g.MemFacts m1) (k : Nat) (hk : k < g.n)
    (s : State) (h : LoopInv g m1 k s) :
    WP isa body s (fun s' => ∃ k', k < k' ∧ k' ≤ g.n ∧ LoopInv g m1 k' s' ∧
      s'.zf = some (BitVec.ofNat 64 (g.n - k') == 0#64)) := by
  have hn := hwf.hn
  have hms : g.MemFacts s.mem := hm1.agree hwf h.agree
  unfold body
  apply WP.seq
  obtain ⟨q1, hq1, z1, g1, v1, mm1, rd1, wr1, l1⟩ := parity_exec s
  refine WP.block_intro q1 hq1 ?_
  have hz1 : q1.1.zf = some (decide ((g.n - k) % 2 = 0)) := by
    rw [z1, h.rdx, parity_bit _ (by omega)]
  have gv1 : ∀ v, q1.1.getV v = s.getV v := fun v => by simp only [State.getV, v1]
  apply WP.seq
  by_cases hodd : (g.n - k) % 2 = 1
  · -- one block
    refine WP.ite true (by rw [ne_eval _ _ hz1]; simp [hodd]) (fun _ => ?_) (fun h' => absurd h' (by simp))
    obtain ⟨q2, hq2, hy, hv, g2, m2, rd2, wr2, l2⟩ := load1_exec q1.1 _ (by rw [g1, h.rsi])
      (fun j hj => load_perm g q1.1 (rd1.trans h.rd) k j (by omega) (by omega))
    refine WP.block_intro q2 hq2 ?_
    apply WP.seq
    have hL : ∀ j < 4, HoldsGroup (vpshufbV (q2.1.getV (ymm j)) (maskV bswapMask))
        (Wt (g.Mb k)) (Wt (g.Mb k)) j := by
      intro j hj
      rw [hy j hj, mm1, addr_add_ofNat]
      exact holds_of_msg s.mem g.msg g.n g.inp hms.msg k k j hk hk hj
    refine WP.mono (mid_ok g hwf m1 hm1 k k hk hk s q2.1 h hL (g2.trans g1) (m2.trans mm1)
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (rd2.trans rd1) (wr2.trans wr1) (l2.trans l1)) ?_
    intro s5 h5
    refine WP.ite true (by rw [ne_eval _ _ h5.zf]; simp [hodd]) (fun _ => ?_) (fun h' => absurd h' (by simp))
    obtain ⟨q6, hq6, g6, z6, v6, m6, rd6, wr6, l6⟩ := tail1_exec s5
    have gv6 : ∀ v, q6.1.getV v = s5.getV v := fun v => by simp only [State.getV, v6]
    have e : BitVec.ofNat 64 (g.n - k) - 1#64 = BitVec.ofNat 64 (g.n - (k + 1)) := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_ofNat _ _ (by omega) (by omega)]; congr 1 <;> omega
    refine WP.block_intro q6 hq6 ⟨k + 1, by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi; have := h5.regs i hi; rw [g6]; interval_cases i <;> exact this
    · rw [m6]; exact h5.hmem
    · rw [g6]; exact h5.rsp
    · rw [g6]; exact h5.rdi
    · rw [g6]; simp only; rw [h5.rsi, BitVec.add_assoc, show (64#64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat']; congr 2
    · rw [g6]; simp only; rw [h5.rdx, e]
    · rw [gv6]; exact h5.y10
    · rw [gv6]; exact h5.y11
    · rw [gv6]; exact h5.y12
    · rw [m6]; exact h5.agree
    · rw [rd6]; exact h5.rd
    · rw [wr6]; exact h5.wr
    · rw [l6]; exact h5.labels
    · rw [z6, h5.rdx, e]
  · -- two blocks
    have hev : (g.n - k) % 2 = 0 := by omega
    have hk1 : k + 1 < g.n := by omega
    refine WP.ite false (by rw [ne_eval _ _ hz1]; simp [hev]) (fun h' => absurd h' (by simp)) (fun _ => ?_)
    obtain ⟨q2, hq2, hy, hv, g2, m2, rd2, wr2, l2⟩ := load2_exec q1.1 _ (by rw [g1, h.rsi])
      (fun j hj => load_perm g q1.1 (rd1.trans h.rd) k j (by omega) (by omega))
    refine WP.block_intro q2 hq2 ?_
    apply WP.seq
    have hL : ∀ j < 4, HoldsGroup (vpshufbV (q2.1.getV (ymm j)) (maskV bswapMask))
        (Wt (g.Mb k)) (Wt (g.Mb (k + 1))) j := by
      intro j hj
      rw [hy j hj, mm1, addr_add_ofNat, addr_add_ofNat,
        show 64 * k + 16 * (j + 4) = 64 * (k + 1) + 16 * j by omega]
      exact holds_of_msg s.mem g.msg g.n g.inp hms.msg k (k + 1) j hk hk1 hj
    refine WP.mono (mid_ok g hwf m1 hm1 k (k + 1) hk hk1 s q2.1 h hL (g2.trans g1) (m2.trans mm1)
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (by rw [hv _ (by decide) (by decide) (by decide) (by decide), gv1])
      (rd2.trans rd1) (wr2.trans wr1) (l2.trans l1)) ?_
    intro s5 h5
    refine WP.ite false (by rw [ne_eval _ _ h5.zf]; simp [hev]) (fun h' => absurd h' (by simp)) (fun _ => ?_)
    apply WP.block_append
    have hsep : Mem.Sep g.sp 512 g.st 32 := sep_shrink hwf.sep_sp_st 512 (by omega) (by omega) (by omega)
    refine WP.mono (lane1_ok (g.Hb (k + 1)) (g.Mb (k + 1)) (msgBlock_length _ _) (Wt (g.Mb k)) g.sp g.st []
      hsep s5 h5.regs h5.hmem h5.buf h5.rsp h5.rdi (by rw [h5.wr]; rfl)) ?_
    intro s6 h6
    obtain ⟨q7, hq7, g7, z7, v7, m7, rd7, wr7, l7⟩ := tail2_exec s6
    have gv7 : ∀ v, q7.1.getV v = s6.getV v := fun v => by simp only [State.getV, v7]
    have e : BitVec.ofNat 64 (g.n - k) - 2#64 = BitVec.ofNat 64 (g.n - (k + 2)) := by
      rw [show (2#64) = BitVec.ofNat 64 2 from rfl, ofNat_sub_ofNat _ _ (by omega) (by omega)]; congr 1 <;> omega
    refine WP.block_intro q7 hq7 ⟨k + 2, by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi; have := h6.regs i hi; rw [g7, ← Hb_succ]; interval_cases i <;> exact this
    · rw [m7, ← Hb_succ]; exact h6.hmem
    · rw [g7]; simp only; rw [h6.rsp]; exact h5.rsp
    · rw [g7]; simp only; rw [h6.rdi]; exact h5.rdi
    · rw [g7]; simp only; rw [h6.rsi, h5.rsi, BitVec.add_assoc, show (128#64) = BitVec.ofNat 64 128 from rfl, ofNat_add_ofNat']; congr 2
    · rw [g7]; simp only; rw [h6.rdx, h5.rdx, e]
    · rw [gv7, h6.y10]; exact h5.y10
    · rw [gv7, h6.y11]; exact h5.y11
    · rw [gv7, h6.y12]; exact h5.y12
    · rw [m7]; exact h5.agree.trans h6.mem
    · rw [rd7, h6.rd]; exact h5.rd
    · rw [wr7, h6.wr]; exact h5.wr
    · rw [l7, h6.labels]; exact h5.labels
    · rw [z7, h6.rdx, h5.rdx, e]

end CC.X86.SHA256Avx2
