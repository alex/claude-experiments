import ClaudeCrypto.X86.SHA256.Avx2Phases
import ClaudeCrypto.X86.SHA256.Avx2Load

/-! # AVX2 SHA-256: whole lanes -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

theorem sep_sub {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) (j k' : Nat) (hj : j + k' ≤ k)
    (hn : 0 < n) (hk' : 0 < k') : Mem.Sep a n (b + BitVec.ofNat 64 j) k' := by
  simpa using h.mono 0 j n k' (by omega) hj hn hk'

theorem sep_sub' {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) (j n' : Nat) (hj : j + n' ≤ n)
    (hn : 0 < n') (hk : 0 < k) : Mem.Sep (a + BitVec.ofNat 64 j) n' b k := by
  simpa using h.mono j 0 n' k hj (by omega) hn hk

theorem lane0_rounds (s0 : State) (H MA : List Word) (hM : MA.length = 16) (WB : Nat → Word)
    (hRB : Recur WB) (sp : Addr) (rest : List Region) (hk : KFacts s0 sp) (s : State)
    (h : L0Inv s0 H MA WB sp rest 0 s) :
    WP isa (.block ((List.range 64).map lane0Round).flatten) s (L0Inv s0 H MA WB sp rest 64) := by
  have := WP.block_iter (M := isa) lane0Round (L0Inv s0 H MA WB sp rest) 0 64
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := l0_step s0 H MA hM WB hRB sp rest hk (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') s h
  simpa using this

/-- The invariant of lane 1 before round `t`. -/
structure L1Inv (s0 : State) (H MB : List Word) (WA : Nat → Word) (sp : Addr) (rest : List Region)
    (t : Nat) (s : State) : Prop where
  regs : RegsAt H MB t s.gpr
  rsp : s.gpr.rsp = sp
  rdi : s.gpr.rdi = s0.gpr.rdi
  rsi : s.gpr.rsi = s0.gpr.rsi
  rdx : s.gpr.rdx = s0.gpr.rdx
  vec : s.vec = s0.vec
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = ⟨sp, 560⟩ :: rest
  labels : s.labels = s0.labels

theorem lane1_rounds (s0 : State) (H MB : List Word) (hM : MB.length = 16) (WA : Nat → Word)
    (sp : Addr) (rest : List Region) (hbuf : BufInv WA (Wt MB) s0.mem sp 16) (s : State)
    (h : L1Inv s0 H MB WA sp rest 0 s) :
    WP isa (.block ((List.range 64).map (roundCode 1)).flatten) s (L1Inv s0 H MB WA sp rest 64) := by
  have := WP.block_iter (M := isa) (roundCode 1) (L1Inv s0 H MB WA sp rest) 0 64
    (fun i hi s hs => by
      have hwk : s.mem.readW (sp + BitVec.ofNat 64 (wkOff 1 (0 + i))) 32 = Wt MB (0 + i) + K[0 + i]! := by
        have := hbuf (0 + i) (by omega) 1 (by decide); rw [hs.mem]; simpa [WL] using this
      obtain ⟨q, hq, hr, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        round_regs H MB hM 1 (0 + i) (by decide) (by omega) sp rest s hs.regs hwk hs.rsp hs.wr
      exact WP.block_intro q hq ⟨hr, h1.trans hs.rsp, h2.trans hs.rdi, h3.trans hs.rsi, h4.trans hs.rdx,
        h5.trans hs.vec, h6.trans hs.mem, h7.trans hs.rd, h8.trans hs.wr, h9.trans hs.labels⟩) s h
  simpa using this

/-- What a lane leaves behind. -/
structure LaneOut (H' : List Word) (st sp : Addr) (sI : State) (s : State) : Prop where
  regs : ∀ i < 8, s.gpr.get (hReg i) = (H'[i]!).setWidth 64
  hmem : ∀ i < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H'[i]!
  rsp : s.gpr.rsp = sI.gpr.rsp
  rdi : s.gpr.rdi = sI.gpr.rdi
  rsi : s.gpr.rsi = sI.gpr.rsi
  rdx : s.gpr.rdx = sI.gpr.rdx
  y10 : s.getV .y10 = sI.getV .y10
  y11 : s.getV .y11 = sI.getV .y11
  y12 : s.getV .y12 = sI.getV .y12
  mem : Mem.AgreeL sI.mem s.mem [⟨sp, 512⟩, ⟨st, 32⟩]
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  labels : s.labels = sI.labels

theorem agreeL_two {m m' m'' : Mem} {sp st : Addr} (h1 : Mem.Agree m m' ⟨sp, 512⟩)
    (h2 : Mem.Agree m' m'' ⟨st, 32⟩) : Mem.AgreeL m m'' [⟨sp, 512⟩, ⟨st, 32⟩] :=
  (Mem.AgreeL.of_agree _ h1 (by simp)).trans (Mem.AgreeL.of_agree _ h2 (by simp))

/-- The hash value survives writes to the stack buffer. -/
theorem hmem_of_agree {m m' : Mem} {sp st : Addr} (hsep : Mem.Sep sp 512 st 32)
    (h : Mem.Agree m m' ⟨sp, 512⟩) (H : List Word)
    (hH : ∀ i < 8, m.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H[i]!) :
    ∀ i < 8, m'.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H[i]! := by
  intro i hi
  rw [h.readW _ _ (sep_sub hsep (4 * i) 4 (by omega) (by omega) (by omega)), hH i hi]

/-- The stack buffer survives writes to the hash value. -/
theorem buf_of_agree {WA WB : Nat → Word} {m m' : Mem} {sp st : Addr} (hsep : Mem.Sep sp 512 st 32)
    (h : Mem.Agree m m' ⟨st, 32⟩) (hb : BufInv WA WB m sp 16) : BufInv WA WB m' sp 16 := by
  intro t ht L hL
  rw [h.readW _ _ (sep_sub hsep.symm (wkOff L t) 4 (by unfold wkOff; omega) (by omega) (by omega)),
    hb t ht L hL]

theorem lane0_ok (H MA : List Word) (hM : MA.length = 16) (WB : Nat → Word) (hRB : Recur WB)
    (sp st : Addr) (rest : List Region) (hsep : Mem.Sep sp 512 st 32) (sI : State) (hk : KFacts sI sp)
    (hr : ∀ i < 8, sI.gpr.get (hReg i) = (H[i]!).setWidth 64)
    (hH : ∀ i < 8, sI.mem.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H[i]!)
    (hwin : ∀ j < 4, HoldsGroup (sI.getV (ymm j)) (Wt MA) WB j)
    (hbuf : BufInv (Wt MA) WB sI.mem sp 4)
    (m10 : sI.getV .y10 = maskV shuf00BA) (m11 : sI.getV .y11 = maskV shufDC00)
    (hrsp : sI.gpr.rsp = sp) (hrdi : sI.gpr.rdi = st) (hwr : sI.wr = ⟨sp, 560⟩ :: ⟨st, 32⟩ :: rest) :
    WP isa (.block lane0) sI (fun s => LaneOut (compress H MA) st sp sI s ∧ BufInv (Wt MA) WB s.mem sp 16) := by
  unfold lane0
  apply WP.block_append
  apply WP.block_append
  obtain ⟨q1, hq1, hr1, rsp1, rdi1, rsi1, rdx1, vec1, mem1, rd1, wr1, lab1⟩ := laneInit_exec H MA sI hr
  refine WP.block_intro q1 hq1 ?_
  have gv : ∀ v, q1.1.getV v = sI.getV v := fun v => by simp only [State.getV, vec1]
  have h0 : L0Inv sI H MA WB sp (⟨st, 32⟩ :: rest) 0 q1.1 := by
    refine ⟨hr1, ?_, fun _ => ?_, by rw [gv]; exact m10, by rw [gv]; exact m11, gv _, rsp1.trans hrsp,
      rdi1, rsi1, rdx1, ?_, rd1, wr1.trans hwr, lab1⟩
    · rw [mem1]; exact hbuf
    · unfold WinInv
      simp only [Nat.zero_div, Nat.zero_mod, Nat.reduceAdd, Nat.reduceMod, gv]
      exact ⟨hwin 1 (by decide), hwin 2 (by decide), hwin 3 (by decide), fun _ => hwin 0 (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    · rw [mem1]; exact Mem.Agree.refl _ _
  refine WP.mono (lane0_rounds sI H MA hM WB hRB sp _ hk q1.1 h0) ?_
  intro s hs
  obtain ⟨q2, hq2, hr2, hm2, hag2, rsp2, rdi2, rsi2, rdx2, vec2, rd2, wr2, lab2⟩ :=
    laneFinish_exec H MA s st sp rest hs.regs (hs.rdi.trans hrdi) hs.wr
      (hmem_of_agree hsep hs.mem H hH)
  have gv2 : ∀ v, q2.1.getV v = s.getV v := fun v => by simp only [State.getV, vec2]
  refine WP.block_intro q2 hq2 ⟨⟨hr2, hm2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, agreeL_two hs.mem hag2, ?_, ?_, ?_⟩, ?_⟩
  · rw [rsp2, hs.rsp, hrsp]
  · rw [rdi2, hs.rdi]
  · rw [rsi2, hs.rsi]
  · rw [rdx2, hs.rdx]
  · rw [gv2, hs.m10, m10]
  · rw [gv2, hs.m11, m11]
  · rw [gv2, hs.y12]
  · rw [rd2, hs.rd]
  · rw [wr2, hs.wr, hwr]
  · rw [lab2, hs.labels]
  · have hb := hs.buf
    simp only [Nat.reduceDiv, Nat.reduceAdd, Nat.reduceLeDiff, Nat.min_def, reduceIte] at hb
    exact buf_of_agree hsep hag2 hb

theorem lane1_ok (H MB : List Word) (hM : MB.length = 16) (WA : Nat → Word)
    (sp st : Addr) (rest : List Region) (hsep : Mem.Sep sp 512 st 32) (sI : State)
    (hr : ∀ i < 8, sI.gpr.get (hReg i) = (H[i]!).setWidth 64)
    (hH : ∀ i < 8, sI.mem.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H[i]!)
    (hbuf : BufInv WA (Wt MB) sI.mem sp 16)
    (hrsp : sI.gpr.rsp = sp) (hrdi : sI.gpr.rdi = st) (hwr : sI.wr = ⟨sp, 560⟩ :: ⟨st, 32⟩ :: rest) :
    WP isa (.block lane1) sI (LaneOut (compress H MB) st sp sI) := by
  unfold lane1
  apply WP.block_append
  apply WP.block_append
  obtain ⟨q1, hq1, hr1, rsp1, rdi1, rsi1, rdx1, vec1, mem1, rd1, wr1, lab1⟩ := laneInit_exec H MB sI hr
  refine WP.block_intro q1 hq1 ?_
  have h0 : L1Inv q1.1 H MB WA sp (⟨st, 32⟩ :: rest) 0 q1.1 :=
    ⟨hr1, rsp1.trans hrsp, rfl, rfl, rfl, rfl, rfl, rfl, wr1.trans hwr, rfl⟩
  refine WP.mono (lane1_rounds q1.1 H MB hM WA sp _ (by rw [mem1]; exact hbuf) q1.1 h0) ?_
  intro s hs
  have hH' : ∀ i < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * i)) 32 = H[i]! := by
    rw [hs.mem, mem1]; exact hH
  obtain ⟨q2, hq2, hr2, hm2, hag2, rsp2, rdi2, rsi2, rdx2, vec2, rd2, wr2, lab2⟩ :=
    laneFinish_exec H MB s st sp rest hs.regs (hs.rdi.trans (rdi1.trans hrdi)) hs.wr hH'
  have gv2 : ∀ v, q2.1.getV v = sI.getV v := fun v => by simp only [State.getV, vec2, hs.vec, vec1]
  refine WP.block_intro q2 hq2 ⟨hr2, hm2, ?_, ?_, ?_, ?_, gv2 _, gv2 _, gv2 _, ?_, ?_, ?_, ?_⟩
  · rw [rsp2, hs.rsp, hrsp]
  · rw [rdi2, hs.rdi, rdi1]
  · rw [rsi2, hs.rsi, rsi1]
  · rw [rdx2, hs.rdx, rdx1]
  · rw [← mem1, ← hs.mem]; exact Mem.AgreeL.of_agree _ hag2 (by simp)
  · rw [rd2, hs.rd, rd1]
  · rw [wr2, hs.wr, hwr]
  · rw [lab2, hs.labels, lab1]

end CC.X86.SHA256Avx2
