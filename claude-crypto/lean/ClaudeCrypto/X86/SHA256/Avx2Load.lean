import ClaudeCrypto.X86.SHA256.Avx2Lane

/-! # AVX2 SHA-256: loading and preparing the message blocks -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

set_option maxHeartbeats 4000000

theorem lane32_append128 (hi lo : BitVec 128) (i : Nat) (hi8 : i < 8) :
    lane 32 (hi ++ lo : BitVec 256) i = if i < 4 then lane 32 lo i else lane 32 hi (i - 4) := by
  apply eq_of_getLsbD_eq; intro k hk
  by_cases h : i < 4
  · simp only [h, ite_true, lane, getLsbD_extractLsb', getLsbD_append, hk, decide_true, Bool.true_and,
      show 32 * i + k < 128 by omega]
  · simp only [h, ite_false, lane, getLsbD_extractLsb', getLsbD_append, hk, decide_true, Bool.true_and,
      show ¬ 32 * i + k < 128 by omega, show 32 * i + k - 128 = 32 * (i - 4) + k by omega,
      show 32 * (i - 4) + k < 128 by omega]

theorem lane32_readW128 (m : Mem) (a : Addr) (r : Nat) (hr : r < 4) :
    lane 32 (m.readW a 128) r = m.readW (a + BitVec.ofNat 64 (4 * r)) 32 := by
  unfold Mem.readW
  show lane 32 (setWidth 128 (m.read a 16)) r = setWidth 32 (m.read (a + BitVec.ofNat 64 (4 * r)) 4)
  rw [Mem.read_sub m a 16 (4 * r) 4 (by omega) (by decide)]
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_setWidth, getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    show 32 * r + k < 128 by omega, show k < 8 * 4 by omega]
  congr 1; omega

theorem getV_setV_same (s : State) (v : VReg) (x : BitVec 256) : (s.setV v x).getV v = x := by
  cases v <;> rfl

theorem getV_setV_ne (s : State) (v w : VReg) (x : BitVec 256) (h : w ≠ v) :
    (s.setV v x).getV w = s.getV w := by
  cases v <;> cases w <;> first | rfl | exact absurd rfl h

/-- Load two blocks: block at `p` into the low lanes, block at `p + 64` into the high lanes. -/
theorem load2_exec (s : State) (p : Addr) (hrsi : s.gpr.rsi = p)
    (hperm : ∀ j < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * j)) 16) :
    ∃ q, execBlock isa load2 s = some q ∧
      (∀ j < 4, q.1.getV (ymm j) = s.mem.readW (p + BitVec.ofNat 64 (16 * (j + 4))) 128 ++
        s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128) ∧
      (∀ v, v ≠ .y0 → v ≠ .y1 → v ≠ .y2 → v ≠ .y3 → q.1.getV v = s.getV v) ∧
      q.1.gpr = s.gpr ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have q0 := hperm 0 (by decide); have q1 := hperm 1 (by decide); have q2 := hperm 2 (by decide)
  have q3 := hperm 3 (by decide); have q4 := hperm 4 (by decide); have q5 := hperm 5 (by decide)
  have q6 := hperm 6 (by decide); have q7 := hperm 7 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at q0 q1 q2 q3 q4 q5 q6 q7
  simp only [load2, ymm, List.range, List.range.loop, List.map, List.flatten, Nat.reduceMul,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, List.append_eq, List.cons_append, List.nil_append, List.append_nil]
  x86_sym [hrsi, q0, q1, q2, q3, q4, q5, q6, q7]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro j hj
    interval_cases j <;> simp only [State.getV, VRegs.get, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] <;> x86_sym
  · intro v h0 h1 h2 h3
    cases v <;> first | rfl | exact absurd rfl h0 | exact absurd rfl h1 | exact absurd rfl h2 |
      exact absurd rfl h3

/-- Load one block into both lanes. -/
theorem load1_exec (s : State) (p : Addr) (hrsi : s.gpr.rsi = p)
    (hperm : ∀ j < 4, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * j)) 16) :
    ∃ q, execBlock isa load1 s = some q ∧
      (∀ j < 4, q.1.getV (ymm j) = s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128 ++
        s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128) ∧
      (∀ v, v ≠ .y0 → v ≠ .y1 → v ≠ .y2 → v ≠ .y3 → q.1.getV v = s.getV v) ∧
      q.1.gpr = s.gpr ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have q0 := hperm 0 (by decide); have q1 := hperm 1 (by decide); have q2 := hperm 2 (by decide)
  have q3 := hperm 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at q0 q1 q2 q3
  simp only [load1, ymm, List.range, List.range.loop, List.map, Nat.reduceMul,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero]
  x86_sym [hrsi, q0, q1, q2, q3]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro j hj
    interval_cases j <;> simp only [State.getV, VRegs.get, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero] <;> x86_sym
  · intro v h0 h1 h2 h3
    cases v <;> first | rfl | exact absurd rfl h0 | exact absurd rfl h1 | exact absurd rfl h2 |
      exact absurd rfl h3

/-! ## Preparing words 0–15 -/

def prepJ (j : Nat) : List Instr :=
  [ .vpshufb (ymm j) (ymm j) .y12,
    .vpaddd .y4 (ymm j) (.mem (ripAt kLabel (32 * j))),
    .vstore256 (rspAt (32 * j)) .y4 ]

theorem prep_eq : prep = ((List.range 4).map fun j => prepJ (0 + j)).flatten := rfl

theorem prepJ_eq (j : Nat) (hj : j < 4) : prepJ j = [.vpshufb (ymm j) (ymm j) .y12] ++ schedSlice j 3 := by
  interval_cases j <;> rfl

/-- The invariant of the `prep` phase after `j` groups. -/
structure PrepInv (WA WB : Nat → Word) (sp : Addr) (s0 sI : State) (j : Nat) (s : State) : Prop where
  done : ∀ i < j, HoldsGroup (s.getV (ymm i)) WA WB i
  todo : ∀ i, j ≤ i → i < 4 → s.getV (ymm i) = sI.getV (ymm i)
  buf : BufInv WA WB s.mem sp j
  mem : Mem.Agree s0.mem s.mem ⟨sp, 512⟩
  gpr : s.gpr = sI.gpr
  y10 : s.getV .y10 = sI.getV .y10
  y11 : s.getV .y11 = sI.getV .y11
  y12 : s.getV .y12 = sI.getV .y12
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  labels : s.labels = sI.labels

theorem ymm_lt4_ne (i : Nat) (hi : i < 4) : ymm i ≠ .y10 ∧ ymm i ≠ .y11 ∧ ymm i ≠ .y12 := by
  interval_cases i <;> decide

theorem prep_step (WA WB : Nat → Word) (sp : Addr) (rest : List Region) (s0 sI : State)
    (hk : KFacts s0 sp)
    (hx : ∀ j < 4, HoldsGroup (vpshufbV (sI.getV (ymm j)) (maskV bswapMask)) WA WB j)
    (h12 : sI.getV .y12 = maskV bswapMask) (hrsp : sI.gpr.rsp = sp) (hwr : sI.wr = ⟨sp, 560⟩ :: rest)
    (hrd : sI.rd = s0.rd) (hlab : sI.labels = s0.labels)
    (j : Nat) (hj : j < 4) (s : State) (h : PrepInv WA WB sp s0 sI j s) :
    ∃ q, execBlock isa (prepJ j) s = some q ∧ PrepInv WA WB sp s0 sI (j + 1) q.1 := by
  rw [prepJ_eq j hj, execBlock_append]
  have hv : execBlock isa [.vpshufb (ymm j) (ymm j) .y12] s =
      some (s.setV (ymm j) (vpshufbV (s.getV (ymm j)) (s.getV .y12)), []) := by
    simp [execBlock, isa, exec, Instr.sz, execW, execV, addrs]
  rw [hv, Option.bind_some]
  set s1 := s.setV (ymm j) (vpshufbV (s.getV (ymm j)) (s.getV .y12)) with hs1
  have hjm : j % 4 = j := Nat.mod_eq_of_lt hj
  have hkr : InRegions s1.rd (kAddr s1 j) 32 := by
    simp only [hs1, State.setV, kAddr]; rw [h.rd, hrd, h.labels, hlab]; exact hk.rd _ (by omega)
  obtain ⟨q, hq, hf, h0, hm⟩ := slice3_exec j (by omega) sp rest s1 hkr
    (by simp only [hs1, State.setV]; rw [h.gpr, hrsp]) (by simp only [hs1, State.setV]; rw [h.wr, hwr])
  rw [hq]
  refine ⟨_, rfl, ?_⟩
  rw [hjm] at h0 hm
  have e1 : s1.getV (ymm j) = vpshufbV (sI.getV (ymm j)) (maskV bswapMask) := by
    rw [hs1, getV_setV_same, h.todo j (le_refl _) hj, h.y12, h12]
  obtain ⟨g1, -, -, -, -, rd1, wr1, lab1, -⟩ := id hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hij : i = j
    · subst hij; rw [h0, e1]; exact hx i hj
    · rw [hf.ymm i (by omega) (by rw [hjm]; exact hij), hs1, getV_setV_ne _ _ _ _ (ymm_ne _ _ (by omega) hj hij)]
      exact h.done i (by omega)
  · intro i hi hi4
    rw [hf.ymm i hi4 (by rw [hjm]; omega), hs1, getV_setV_ne _ _ _ _ (ymm_ne _ _ hi4 hj (by omega))]
    exact h.todo i (by omega) hi4
  · rw [hm]
    refine h.buf.step (by omega) _ _ (by rw [e1]; exact hx j hj) ?_
    intro i hi
    have e : kAddr s1 j = kAddr s0 j := by
      simp only [hs1, State.setV, kAddr]; rw [h.labels, hlab]
    have hsep := hk.sep j (by omega)
    rw [e]
    show lane 32 (s.mem.readW (kAddr s0 j) 256) i = _
    rw [h.mem.readW (kAddr s0 j) 256 hsep]
    exact hk.val j (by omega) i hi
  · rw [hm]; refine h.mem.writeW _ _ ?_; exact region_contains_buf sp _ (by omega)
  · rw [g1]; exact h.gpr
  · rw [hf.high _ (by simp), hs1, getV_setV_ne _ _ _ _ (ymm_lt4_ne j hj).1.symm]; exact h.y10
  · rw [hf.high _ (by simp), hs1, getV_setV_ne _ _ _ _ (ymm_lt4_ne j hj).2.1.symm]; exact h.y11
  · rw [hf.high _ (by simp), hs1, getV_setV_ne _ _ _ _ (ymm_lt4_ne j hj).2.2.symm]; exact h.y12
  · rw [rd1]; exact h.rd
  · rw [wr1]; exact h.wr
  · rw [lab1]; exact h.labels

theorem prep_ok (WA WB : Nat → Word) (sp : Addr) (rest : List Region) (s0 sI : State)
    (hk : KFacts s0 sp)
    (hx : ∀ j < 4, HoldsGroup (vpshufbV (sI.getV (ymm j)) (maskV bswapMask)) WA WB j)
    (h12 : sI.getV .y12 = maskV bswapMask) (hrsp : sI.gpr.rsp = sp) (hwr : sI.wr = ⟨sp, 560⟩ :: rest)
    (hrd : sI.rd = s0.rd) (hlab : sI.labels = s0.labels) (hmem : Mem.Agree s0.mem sI.mem ⟨sp, 512⟩) :
    WP isa (.block prep) sI (PrepInv WA WB sp s0 sI 4) := by
  rw [prep_eq]
  have := WP.block_iter (M := isa) prepJ (PrepInv WA WB sp s0 sI) 0 4
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := prep_step WA WB sp rest s0 sI hk hx h12 hrsp hwr hrd hlab (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') sI
    ⟨fun i hi => absurd hi (by omega), fun _ _ _ => rfl, fun t ht => absurd ht (by omega), hmem, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  simpa using this

/-! ## The message words -/

theorem ofNat_add_ofNat' (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem msg_word (m : Mem) (msg : List (BitVec 8)) (n : Nat) (inp : Addr)
    (hmsg : ∀ i < 64 * n, m (inp + BitVec.ofNat 64 i) = msg[i]!) (blk w : Nat) (hblk : blk < n) (hw : w < 16) :
    bswap32 (m.readW (inp + BitVec.ofNat 64 (64 * blk + 4 * w)) 32) = Wt (msgBlock msg blk) w := by
  rw [Wt_lt _ _ hw, msgBlock_getElem _ _ _ hw, bswap32_readW]
  have e : ∀ k, inp + BitVec.ofNat 64 (64 * blk + 4 * w) + BitVec.ofNat 64 k =
      inp + BitVec.ofNat 64 (64 * blk + 4 * w + k) := fun k => by rw [BitVec.add_assoc, ofNat_add_ofNat']
  have e1 : inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 1 = inp + BitVec.ofNat 64 (64 * blk + 4 * w + 1) := e 1
  have e2 : inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 2 = inp + BitVec.ofNat 64 (64 * blk + 4 * w + 2) := e 2
  have e3 : inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 3 = inp + BitVec.ofNat 64 (64 * blk + 4 * w + 3) := e 3
  rw [e1, e2, e3, hmsg _ (by omega), hmsg _ (by omega), hmsg _ (by omega), hmsg _ (by omega)]
  simp only [msgWord, wordBE, show 64 * blk + 4 * w + 1 = 64 * blk + 4 * w + 1 from rfl]

/-- The byte-swapped vector of a pair of message rows is a schedule group. -/
theorem holds_of_msg (m : Mem) (msg : List (BitVec 8)) (n : Nat) (inp : Addr)
    (hmsg : ∀ i < 64 * n, m (inp + BitVec.ofNat 64 i) = msg[i]!) (blkA blkB j : Nat)
    (hA : blkA < n) (hB : blkB < n) (hj : j < 4) :
    HoldsGroup (vpshufbV (m.readW (inp + BitVec.ofNat 64 (64 * blkB + 16 * j)) 128 ++
        m.readW (inp + BitVec.ofNat 64 (64 * blkA + 16 * j)) 128) (maskV bswapMask))
      (Wt (msgBlock msg blkA)) (Wt (msgBlock msg blkB)) j := by
  intro i hi
  rw [lane_bswap _ _ hi, lane32_append128 _ _ _ hi]
  unfold sel
  by_cases h4 : i < 4
  · simp only [h4, ite_true]
    rw [lane32_readW128 _ _ _ h4, BitVec.add_assoc, ofNat_add_ofNat',
      show 64 * blkA + 16 * j + 4 * i = 64 * blkA + 4 * (4 * j + i % 4) by omega]
    exact msg_word m msg n inp hmsg blkA _ hA (by omega)
  · simp only [h4, ite_false]
    rw [lane32_readW128 _ _ _ (by omega), BitVec.add_assoc, ofNat_add_ofNat',
      show 64 * blkB + 16 * j + 4 * (i - 4) = 64 * blkB + 4 * (4 * j + i % 4) by omega]
    exact msg_word m msg n inp hmsg blkB _ hB (by omega)

end CC.X86.SHA256Avx2
