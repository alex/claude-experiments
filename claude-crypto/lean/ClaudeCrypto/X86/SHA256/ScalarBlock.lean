import ClaudeCrypto.X86.SHA256.ScalarProof
import ClaudeCrypto.X86.SHA256.ScalarPhases

/-!
# The x86-64 scalar SHA-256 block function: blocks, loop and whole function
-/

namespace CC.X86.SHA256Scalar

open CC.Spec.SHA256

/-! ## Rounds -/

theorem round_ok (g : Ghost) (blk t : Nat) (ht : t < 64) (hM : (g.Mb blk).length = 16) (mb : Mem)
    (rest : List Region) (hwr : g.wr = ⟨g.sp, 112⟩ :: rest) (s : State)
    (h : RoundInv g blk t mb s) : WP isa (.block (roundAll t)) s (RoundInv g blk (t + 1) mb) := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, hrsp, hrdi, hrsi, hrdx, hag, hrd, hwr'⟩ := h
  obtain ⟨p, hp, hpost⟩ := round_exec t ht (varsAt (g.Hb blk) (g.Mb blk) t) (Wt (g.Mb blk)) g.sp rest s
    ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, fun h16 => Wt_slots _ t h16, hrsp, hwr'.trans hwr⟩
  refine WP.block_intro p hp ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hs', hrsp', hrdi', hrsi', hrdx', hag', hrd', hwr''⟩ := hpost
  have hv := varsAt_succ (g.Hb blk) (g.Mb blk) hM t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs', hrsp', hrdi'.trans hrdi, hrsi'.trans hrsi,
    hrdx'.trans hrdx, hag.trans hag', hrd'.trans hrd, hwr''.trans hwr'⟩ <;> rw [hv] <;> assumption

theorem rounds_ok (g : Ghost) (blk : Nat) (hM : (g.Mb blk).length = 16) (mb : Mem)
    (rest : List Region) (hwr : g.wr = ⟨g.sp, 112⟩ :: rest) (s : State)
    (h : RoundInv g blk 0 mb s) : WP isa (.block rounds) s (RoundInv g blk 64 mb) := by
  have := WP.block_iter (M := isa) roundAll (fun t => RoundInv g blk t mb) 0 64
    (fun i hi s hs => by simpa using round_ok g blk i hi hM mb rest hwr s (by simpa using hs)) s h
  simpa [rounds] using this

/-! ## Address arithmetic -/

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem msg_addr (inp : Addr) (blk j : Nat) :
    inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (4 * j) = inp + BitVec.ofNat 64 (64 * blk + 4 * j) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem sep_zero_add {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) (j k' : Nat) (hj : j + k' ≤ k)
    (hn : 0 < n) (hk' : 0 < k') : Mem.Sep a n (b + BitVec.ofNat 64 j) k' := by
  have := h.mono 0 j n k' (by omega) hj hn hk'
  simpa using this

/-! ## Loading the message block -/

/-- Well-formedness of the ghost state: the function's preconditions. -/
structure Ghost.WF (g : Ghost) : Prop where
  hH : g.H.length = 8
  hlen : g.msg.length = 64 * g.n
  hn : 64 * g.n + 64 < 2 ^ 64
  hwr : g.wr = [⟨g.sp, 112⟩, ⟨g.st, 32⟩]
  hrd : g.rd = [⟨g.inp, 64 * g.n⟩]
  sep_sp_st : Mem.Sep g.sp 112 g.st 32
  sep_sp_inp : Mem.Sep g.sp 112 g.inp (64 * g.n)
  sep_st_inp : Mem.Sep g.st 32 g.inp (64 * g.n)

/-- The invariant at the head of the per-block loop.  `m1` is the memory
after the prologue. -/
structure LoopInv (g : Ghost) (m1 : Mem) (blk : Nat) (s : State) : Prop where
  regs : ∀ k < 8, s.gpr.get (hReg k) = ((g.Hb blk)[k]!).setWidth 64
  hmem : ∀ k < 8, s.mem.readW (g.st + BitVec.ofNat 64 (4 * k)) 32 = (g.Hb blk)[k]!
  rsp : s.gpr.rsp = g.sp
  rdi : s.gpr.rdi = g.st
  rsi : s.gpr.rsi = g.inp + BitVec.ofNat 64 (64 * blk)
  rdx : s.gpr.rdx = BitVec.ofNat 64 (g.n - blk)
  agree : Mem.AgreeL m1 s.mem [⟨g.sp, 64⟩, ⟨g.st, 32⟩]
  rd : s.rd = g.rd
  wr : s.wr = g.wr

theorem Ghost.Hb_length (g : Ghost) (hwf : g.WF) (blk : Nat) : (g.Hb blk).length = 8 := by
  unfold Ghost.Hb stateAfter
  induction blk with
  | zero => simpa using hwf.hH
  | succ k ih => rw [List.range_succ, List.foldl_append]; simp [compress]

theorem region_mem_iff (g : Ghost) (hwf : g.WF) (a : Addr) :
    (∀ r ∈ [(⟨g.sp, 64⟩ : Region), ⟨g.st, 32⟩], Mem.Sep r.base r.len a 4) ↔
      Mem.Sep g.sp 64 a 4 ∧ Mem.Sep g.st 32 a 4 := by simp

theorem msg_bytes (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (m : Mem)
    (hag : Mem.AgreeL m1 m [⟨g.sp, 64⟩, ⟨g.st, 32⟩]) (i : Nat) (hi : i < 64 * g.n) :
    m (g.inp + BitVec.ofNat 64 i) = g.msg[i]! := by
  rw [← hmsg i hi]
  apply hag.apply
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hwf.sep_sp_inp.mono 0 i 64 1 (by omega) (by omega) (by omega) (by omega)).symm.symm |> fun h =>
      by simpa using h
  · exact by simpa using hwf.sep_st_inp.mono 0 i 32 1 (by omega) (by omega) (by omega) (by omega)

theorem msgWord_load (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (m : Mem)
    (hag : Mem.AgreeL m1 m [⟨g.sp, 64⟩, ⟨g.st, 32⟩]) (blk j : Nat) (hblk : blk < g.n) (hj : j < 16) :
    bswap32 (m.readW (g.inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (4 * j)) 32) =
      msgWord g.msg blk j := by
  rw [bswap32_readW, msg_addr]
  have e : ∀ k, g.inp + BitVec.ofNat 64 (64 * blk + 4 * j) + BitVec.ofNat 64 k =
      g.inp + BitVec.ofNat 64 (64 * blk + 4 * j + k) := fun k => by rw [BitVec.add_assoc, ofNat_add_ofNat]
  have e1 : g.inp + BitVec.ofNat 64 (64 * blk + 4 * j) + 1 = g.inp + BitVec.ofNat 64 (64 * blk + 4 * j + 1) := e 1
  have e2 : g.inp + BitVec.ofNat 64 (64 * blk + 4 * j) + 2 = g.inp + BitVec.ofNat 64 (64 * blk + 4 * j + 2) := e 2
  have e3 : g.inp + BitVec.ofNat 64 (64 * blk + 4 * j) + 3 = g.inp + BitVec.ofNat 64 (64 * blk + 4 * j + 3) := e 3
  rw [e1, e2, e3]
  simp only [msgWord, wordBE]
  rw [msg_bytes g hwf m1 hmsg m hag _ (by omega), msg_bytes g hwf m1 hmsg m hag _ (by omega),
    msg_bytes g hwf m1 hmsg m hag _ (by omega), msg_bytes g hwf m1 hmsg m hag _ (by omega)]

theorem Regs.set_rax_set_rax (r : Regs) (x y : BitVec 64) : (r.set .rax x).set .rax y = r.set .rax y := rfl

theorem hReg_ne_rax (k : Nat) (hk : k < 8) : hReg k ≠ .rax := by
  interval_cases k <;> decide

theorem get_set_rax (r : Regs) (x : BitVec 64) (k : Nat) (hk : k < 8) :
    (r.set .rax x).get (hReg k) = r.get (hReg k) := by
  interval_cases k <;> rfl

/-- The invariant during the message-load phase. -/
def LoadInv (g : Ghost) (blk : Nat) (s0 : State) (j : Nat) (s : State) : Prop :=
  (∀ i < j, s.mem.readW (slotAddr g.sp i) 32 = msgWord g.msg blk i) ∧
  Mem.Agree s0.mem s.mem ⟨g.sp, 64⟩ ∧ (∃ x, s.gpr = s0.gpr.set .rax x) ∧ s.rd = s0.rd ∧ s.wr = s0.wr

theorem load_ok (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (blk : Nat) (hblk : blk < g.n)
    (s0 : State) (h0 : LoopInv g m1 blk s0) (j : Nat) (hj : j < 16) (s : State)
    (h : LoadInv g blk s0 j s) : WP isa (.block (loadCode j)) s (LoadInv g blk s0 (j + 1)) := by
  obtain ⟨hslots, hag, ⟨x, hx⟩, hrd, hwr⟩ := h
  have hsep : Mem.Sep g.sp 64 (g.inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (4 * j)) 4 := by
    rw [msg_addr]
    have := hwf.sep_sp_inp.mono 0 (64 * blk + 4 * j) 64 4 (by omega) (by omega) (by omega) (by omega)
    simpa using this
  obtain ⟨q, hq, hmem, hgpr, hrd', hwr', -, -⟩ := load_exec j hj s g.sp (g.inp + BitVec.ofNat 64 (64 * blk))
    [⟨g.st, 32⟩] (s0.mem.readW (g.inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (4 * j)) 32)
    (by rw [hx]; exact h0.rsp) (by rw [hx]; exact h0.rsi) (by rw [hwr, h0.wr, hwf.hwr])
    (by
      rw [hrd, h0.rd, hwf.hrd, msg_addr]
      exact ⟨_, List.mem_singleton_self _,
        Region.contains_offset _ _ _ _ (by omega) (by have := hwf.hn; omega)⟩)
    (hag.readW _ _ hsep)
  refine WP.block_intro q hq ⟨?_, ?_, ⟨_, by rw [hgpr, hx]; rfl⟩, hrd'.trans hrd, hwr'.trans hwr⟩
  · intro i hi
    rw [hmem, msgWord_load g hwf m1 hmsg s0.mem h0.agree blk j hblk hj, Nat.mod_eq_of_lt hj]
    by_cases hij : i = j
    · subst hij; exact Mem.readW_writeW_same_32 _ _ _
    · rw [Mem.readW_writeW_sep _ _ _ _ _ (slotAddr_sep g.sp j i hj (by omega) (Ne.symm hij))]
      exact hslots i (by omega)
  · rw [hmem]
    refine hag.writeW _ _ ?_
    rw [Nat.mod_eq_of_lt hj, region_contains_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

theorem loads_ok (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (blk : Nat) (hblk : blk < g.n)
    (s0 : State) (h0 : LoopInv g m1 blk s0) :
    WP isa (.block loads) s0 (RoundInv g blk 0 s0.mem) := by
  have := WP.block_iter (M := isa) loadCode (LoadInv g blk s0) 0 16
    (fun i hi s hs => by simpa using load_ok g hwf m1 hmsg blk hblk s0 h0 i hi s (by simpa using hs))
    s0 ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Mem.Agree.refl _ _, ⟨s0.gpr.rax, rfl⟩, rfl, rfl⟩
  simp only [Nat.zero_add] at this
  refine WP.mono this ?_
  rintro s ⟨hslots, hag, ⟨x, hx⟩, hrd, hwr⟩
  have hr := fun k hk => (get_set_rax s0.gpr x k hk).trans (h0.regs k hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hag, hrd.trans h0.rd, hwr.trans h0.wr⟩
  · rw [hx]; exact hr 0 (by decide)
  · rw [hx]; exact hr 1 (by decide)
  · rw [hx]; exact hr 2 (by decide)
  · rw [hx]; exact hr 3 (by decide)
  · rw [hx]; exact hr 4 (by decide)
  · rw [hx]; exact hr 5 (by decide)
  · rw [hx]; exact hr 6 (by decide)
  · rw [hx]; exact hr 7 (by decide)
  · intro j hj
    rw [hslots j hj, slotIdx, if_pos (by omega), Wt_lt _ _ hj, Ghost.Mb, msgBlock_getElem _ _ _ hj]
  · rw [hx]; exact h0.rsp
  · rw [hx]; exact h0.rdi
  · rw [hx]; exact h0.rsi
  · rw [hx]; exact h0.rdx

theorem Hb_succ (g : Ghost) (blk : Nat) :
    g.Hb (blk + 1) =
      [(varsAt (g.Hb blk) (g.Mb blk) 64).a + (g.Hb blk)[0]!, (varsAt (g.Hb blk) (g.Mb blk) 64).b + (g.Hb blk)[1]!,
       (varsAt (g.Hb blk) (g.Mb blk) 64).c + (g.Hb blk)[2]!, (varsAt (g.Hb blk) (g.Mb blk) 64).d + (g.Hb blk)[3]!,
       (varsAt (g.Hb blk) (g.Mb blk) 64).e + (g.Hb blk)[4]!, (varsAt (g.Hb blk) (g.Mb blk) 64).f + (g.Hb blk)[5]!,
       (varsAt (g.Hb blk) (g.Mb blk) 64).g + (g.Hb blk)[6]!, (varsAt (g.Hb blk) (g.Mb blk) 64).h + (g.Hb blk)[7]!] := by
  rw [Ghost.Hb, stateAfter_succ, compress_eq]; rfl

theorem ofNat_sub_one (a : Nat) (h1 : 1 ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (1 : BitVec 64).toNat = 1 := rfl
  rw [this]; omega

theorem finish_ok (g : Ghost) (hwf : g.WF) (m1 : Mem) (blk : Nat) (hblk : blk < g.n)
    (s0 : State) (h0 : LoopInv g m1 blk s0) (s : State) (h : RoundInv g blk 64 s0.mem s) :
    WP isa (.block finish) s (fun s' => LoopInv g m1 (blk + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (g.n - (blk + 1)) == 0)) := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, -, hrsp, hrdi, hrsi, hrdx, hag, hrd, hwr⟩ := h
  have hH : ∀ k < 8, s.mem.readW (g.st + BitVec.ofNat 64 (4 * k)) 32 = (g.Hb blk)[k]! := by
    intro k hk
    rw [hag.readW _ _ (by
      have := hwf.sep_sp_st.mono 0 (4 * k) 64 4 (by omega) (by omega) (by omega) (by omega)
      simpa using this)]
    exact h0.hmem k hk
  have hHb := Hb_succ g blk
  generalize varsAt (g.Hb blk) (g.Mb blk) 64 = v at ha hb hc hd he hf hg hh hHb
  obtain ⟨q, hq, h0', h1', h2', h3', h4', h5', h6', h7', m0, m1', m2, m3, m4, m5, m6, m7, hag', hrsp', hrdi',
      hrsi', hrdx', hzf', hrd', hwr'⟩ :=
    finish_exec s g.st g.sp (g.inp + BitVec.ofNat 64 (64 * blk)) [] v (g.Hb blk)
      (BitVec.ofNat 64 (g.n - blk)) ha hb hc hd he hf hg hh hrdi hrsi hrdx
      (by rw [hwr, hwf.hwr]) hH
  have hcnt : BitVec.ofNat 64 (g.n - blk) - 1 = BitVec.ofNat 64 (g.n - (blk + 1)) := by
    rw [ofNat_sub_one _ (by omega) (by have := hwf.hn; omega)]; congr 1
  refine WP.block_intro q hq ⟨⟨?_, ?_, hrsp'.trans hrsp, hrdi', ?_, hrdx'.trans hcnt, ?_,
    hrd'.trans hrd, hwr'.trans hwr⟩, by rw [hzf', hcnt]⟩
  · intro k hk
    rw [hHb]
    interval_cases k <;> assumption
  · intro k hk
    rw [hHb]
    interval_cases k
    · simpa using m0
    · exact m1'
    · exact m2
    · exact m3
    · exact m4
    · exact m5
    · exact m6
    · exact m7
  · rw [hrsi', BitVec.add_assoc, ofNat_add_ofNat]; congr 2
  · exact h0.agree.trans ((Mem.AgreeL.of_agree _ hag (by simp)).trans
      (Mem.AgreeL.of_agree _ hag' (by simp)))

theorem block_ok (g : Ghost) (hwf : g.WF) (m1 : Mem)
    (hmsg : ∀ i < 64 * g.n, m1 (g.inp + BitVec.ofNat 64 i) = g.msg[i]!) (blk : Nat) (hblk : blk < g.n)
    (s : State) (h : LoopInv g m1 blk s) :
    WP isa (.block blockCode) s (fun s' => LoopInv g m1 (blk + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (g.n - (blk + 1)) == 0)) := by
  have hM : (g.Mb blk).length = 16 := msgBlock_length _ _
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (loads_ok g hwf m1 hmsg blk hblk s h) ?_
  intro s1 h1
  refine WP.mono (rounds_ok g blk hM s.mem [⟨g.st, 32⟩] hwf.hwr s1 h1) ?_
  intro s2 h2
  exact finish_ok g hwf m1 blk hblk s h s2 h2

end CC.X86.SHA256Scalar
