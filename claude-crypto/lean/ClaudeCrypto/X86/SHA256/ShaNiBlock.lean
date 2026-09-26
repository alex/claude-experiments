import ClaudeCrypto.X86.SHA256.ShaNiPhases

/-!
# The SHA-NI block function: one block, and the loop

Composition of the phase lemmas (`ShaNiPhases.lean`) with the arithmetic
lemmas (`ShaNiLemmas.lean`), instantiated with the specification's values
(`varsAt`, `Wt`).
-/

namespace CC.X86.SHA256ShaNi

open BitVec CC.X86 CC.Spec.SHA256

/-! ## Frame -/

/-- `s` differs from `s0` only in the vector registers, the flags, `rsi` and `rdx`. -/
structure Frame (s0 s : State) : Prop where
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  gpr : ∀ r, r ≠ .rsi → r ≠ .rdx → s.gpr.get r = s0.gpr.get r

theorem Frame.refl (s : State) : Frame s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-! ## Ghost state -/

/-- The logical inputs of the function. -/
structure Ghost where
  /-- initial hash value (8 words) -/
  H : List Word
  /-- the message, `64 * n` bytes -/
  msg : List (BitVec 8)
  n : Nat
  /-- the state at function entry -/
  s0 : State

namespace Ghost
variable (G : Ghost)
def st : Addr := G.s0.gpr.rdi
def inp : Addr := G.s0.gpr.rsi
def kb : Addr := G.s0.labels kLabel
def bb : Addr := G.s0.labels bswapLabel
def Hb (blk : Nat) : List Word := stateAfter G.H G.msg blk
def Mb (blk : Nat) : List Word := msgBlock G.msg blk
end Ghost

/-- The preconditions relevant to the loop. -/
structure Ghost.WF (G : Ghost) : Prop where
  hlen : G.msg.length = 64 * G.n
  hn : 64 * G.n < 2 ^ 64
  hmsg : ∀ i < 64 * G.n, G.s0.mem (G.inp + BitVec.ofNat 64 i) = G.msg[i]!
  hK : ∀ j < 256, G.s0.mem (G.kb + BitVec.ofNat 64 j) = kTable[j]!
  hB : ∀ j < 16, G.s0.mem (G.bb + BitVec.ofNat 64 j) = bswapMask[j]!
  hrdm : ⟨G.inp, 64 * G.n⟩ ∈ G.s0.rd
  hrdK : ⟨G.kb, 256⟩ ∈ G.s0.rd
  hrdB : ⟨G.bb, 16⟩ ∈ G.s0.rd

theorem inRegions_of_mem {rs rs' : List Region} {r : Region} (h : r ∈ rs) (hl : r.len < 2 ^ 64)
    (k n : Nat) (hk : k + n ≤ r.len) : InRegions (rs ++ rs') (r.base + BitVec.ofNat 64 k) n :=
  ⟨r, List.mem_append_left _ h, Region.contains_offset _ _ _ _ hk hl⟩

/-! ## Constant tables -/

set_option maxRecDepth 100000 in
theorem kTable_words : ∀ w < 64,
    kTable[4 * w + 3]! ++ kTable[4 * w + 2]! ++ kTable[4 * w + 1]! ++ kTable[4 * w]! = K[w]! := by
  decide +kernel

/-- Four round constants, as loaded by `movdqu`. -/
theorem K_vec (G : Ghost) (hwf : G.WF) (j : Nat) (hj : j < 16) :
    G.s0.mem.readW (G.kb + BitVec.ofNat 64 (16 * j)) 128 =
      vec4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
  rw [readW_lanes16]
  rw [lanes_congr 16 _ (fun i => kTable[16 * j + i]!) (fun i hi => by
    rw [add_ofNat_add]; exact hwf.hK _ (by omega))]
  rw [lanes16_vec4]
  have e : ∀ c, c < 4 → kTable[16 * j + (4 * c + 3)]! ++ kTable[16 * j + (4 * c + 2)]! ++
      kTable[16 * j + (4 * c + 1)]! ++ kTable[16 * j + 4 * c]! = K[4 * j + c]! := by
    intro c hc
    have := kTable_words (4 * j + c) (by omega)
    rw [show 4 * (4 * j + c) = 16 * j + 4 * c by ring] at this
    simpa only [Nat.add_assoc] using this
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at e0 e1 e2 e3 ⊢
  rw [e0, e1, e2, e3]

theorem bswap_vec (G : Ghost) (hwf : G.WF) : G.s0.mem.readW G.bb 128 = bswapX := by
  rw [readW_lanes16, bswapX]
  apply lanes_congr
  intro i hi
  exact hwf.hB i hi

/-! ## The message -/

/-- Four message words, as loaded by `movdqu` + `pshufb`. -/
theorem msg_vec (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (k : Nat) (hk : k < 4) :
    pshufb128 (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k)) 128) bswapX =
      packW (Wt (G.Mb blk)) k := by
  rw [readW_lanes16]
  rw [lanes_congr 16 _ (fun i => G.msg[64 * blk + 16 * k + i]!) (fun i hi => by
    rw [add_ofNat_add]; exact hwf.hmsg _ (by omega))]
  rw [pshufb_bswap]
  have hM : ∀ c, c < 4 → Wt (G.Mb blk) (4 * k + c) = msgWord G.msg blk (4 * k + c) := fun c _ => by
    rw [Wt_lt _ _ (by omega), Ghost.Mb, msgBlock_getElem _ _ _ (by omega)]
  have hM0 : Wt (G.Mb blk) (4 * k) = msgWord G.msg blk (4 * k) := hM 0 (by decide)
  rw [packW, hM0, hM 1 (by decide), hM 2 (by decide), hM 3 (by decide)]
  simp only [msgWord, wordBE]
  have i1 : ∀ c, 64 * blk + 4 * (4 * k + c) = 64 * blk + 16 * k + 4 * c := fun c => by ring
  have i0 : 4 * (4 * k) = 16 * k := by ring
  simp only [i0, i1, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]

/-! ## Rounds -/

/-- Two rounds of the specification. -/
theorem varsAt_two (H M : List Word) (hM : M.length = 16) (t : Nat) (ht : t + 1 < 64) :
    varsAt H M (t + 2) = round (round (varsAt H M t) K[t]! (Wt M t)) K[t + 1]! (Wt M (t + 1)) := by
  rw [varsAt_succ _ _ hM _ (by omega), varsAt_succ _ _ hM _ (by omega)]

/-- The schedule registers before the `sha256msg1` of their group is finished. -/
def pend (W : Nat → Word) (k : Nat) : BitVec 128 :=
  if k < 4 then packW W k else sha256msg1 (packW W (k - 4)) (packW W (k - 3))

/-- The invariant before group `j` (rounds `4j .. 4j+3`) of block `blk`. -/
structure GroupInv (G : Ghost) (blk j : Nat) (s : State) : Prop where
  frame : Frame G.s0 s
  y1 : s.getX .y1 = abef (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
  y2 : s.getX .y2 = cdgh (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
  cur : j < 16 → s.getX (wreg j) = packW (Wt (G.Mb blk)) j
  prev : 1 ≤ j → j < 16 → s.getX (wreg (j + 3)) = packW (Wt (G.Mb blk)) (j - 1)
  n1 : j + 1 < 16 → s.getX (wreg (j + 1)) = pend (Wt (G.Mb blk)) (j + 1)
  n2 : j + 2 < 16 → s.getX (wreg (j + 2)) = pend (Wt (G.Mb blk)) (j + 2)
  n3 : j = 0 → s.getX (wreg 3) = packW (Wt (G.Mb blk)) 3
  y8 : s.getX .y8 = bswapX
  y9 : s.getX .y9 = abef (initVars (G.Hb blk))
  y10 : s.getX .y10 = cdgh (initVars (G.Hb blk))
  rsi : s.gpr.rsi = G.inp + BitVec.ofNat 64 (64 * blk)
  rdx : s.gpr.rdx = BitVec.ofNat 64 (G.n - blk)

theorem wreg_mod (k j : Nat) : wreg (k % 4 + j) = wreg (k + j) := by
  unfold wreg; rw [show (k % 4 + j) % 4 = (k + j) % 4 by omega]

theorem wreg_mod0 (k : Nat) : wreg (k % 4) = wreg k := by
  have := wreg_mod k 0; simpa using this

theorem wreg_ne_y8' (k : Nat) : VReg.y8 ≠ wreg k := (wreg_ne_y8 k).symm
theorem wreg_ne_y9' (k : Nat) : VReg.y9 ≠ wreg k := (wreg_ne_y9 k).symm
theorem wreg_ne_y10' (k : Nat) : VReg.y10 ≠ wreg k := (wreg_ne_y10 k).symm

set_option linter.deprecated false in
set_option maxHeartbeats 1000000 in
theorem group_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (j : Nat) (hj : j < 16) (s : State)
    (h : GroupInv G blk j s) : WP isa (.block (groupCode j)) s (GroupInv G blk (j + 1)) := by
  have hM : (G.Mb blk).length = 16 := msgBlock_length _ _
  have hperm : InRegions (s.rd ++ s.wr) (s.labels kLabel + BitVec.ofNat 64 (16 * j)) 16 := by
    rw [h.frame.labels, h.frame.rd]
    exact inRegions_of_mem hwf.hrdK (by norm_num) _ _ (by simp only; omega)
  unfold groupCode
  obtain ⟨q, hq, e2, e1, ew1, ew3, eo, eg, em, erd, ewr, elb⟩ :=
    group_exec (j % 4) (16 * j) (Nat.ble 3 j && Nat.ble j 14) (Nat.ble 1 j && Nat.ble j 12) s hperm
  refine WP.block_intro q hq ?_
  simp only [wreg_mod, wreg_mod0] at e2 e1 ew1 ew3 eo
  -- the values
  set W := Wt (G.Mb blk) with hWdef
  set v := varsAt (G.Hb blk) (G.Mb blk) (4 * j) with hv
  have hK : s.mem.readW (s.labels kLabel + BitVec.ofNat 64 (16 * j)) 128 =
      vec4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
    rw [h.frame.labels, h.frame.mem]; exact K_vec G hwf j hj
  have hwk : padddX (s.mem.readW (s.labels kLabel + BitVec.ofNat 64 (16 * j)) 128) (s.getX (wreg j)) =
      vec4 (K[4 * j]! + W (4 * j)) (K[4 * j + 1]! + W (4 * j + 1)) (K[4 * j + 2]! + W (4 * j + 2))
        (K[4 * j + 3]! + W (4 * j + 3)) := by
    rw [hK, h.cur hj, packW, padddX_vec4]
  have hv2 : varsAt (G.Hb blk) (G.Mb blk) (4 * j + 2) =
      round (round v K[4 * j]! (W (4 * j))) K[4 * j + 1]! (W (4 * j + 1)) :=
    varsAt_two _ _ hM _ (by omega)
  have hv4 : varsAt (G.Hb blk) (G.Mb blk) (4 * (j + 1)) =
      round (round (varsAt (G.Hb blk) (G.Mb blk) (4 * j + 2)) K[4 * j + 2]! (W (4 * j + 2)))
        K[4 * j + 3]! (W (4 * j + 3)) := by
    rw [show 4 * (j + 1) = 4 * j + 2 + 2 by ring, varsAt_two _ _ hM _ (by omega)]
  have hr1 : sha256rnds2 (s.getX .y2) (s.getX .y1)
      (padddX (s.mem.readW (s.labels kLabel + BitVec.ofNat 64 (16 * j)) 128) (s.getX (wreg j))) =
      abef (varsAt (G.Hb blk) (G.Mb blk) (4 * j + 2)) := by
    rw [hwk, h.y1, h.y2, rnds2_eq, hv2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [em]; exact h.frame.mem
  · rw [erd]; exact h.frame.rd
  · rw [ewr]; exact h.frame.wr
  · rw [elb]; exact h.frame.labels
  · intro r h1 h2; rw [eg]; exact h.frame.gpr r h1 h2
  · -- the new (F, E, B, A)
    rw [e1, hr1, hwk, h.y1, pshufd_14, hv2, ← cdgh_round2 v K[4 * j]! K[4 * j + 1]! (W (4 * j))
      (W (4 * j + 1)), rnds2_eq, ← hv2, ← hv4]
  · -- the new (H, G, D, C)
    rw [e2, hr1, hv4, cdgh_round2]
  · -- the current schedule words
    intro hj1
    rw [ew1]
    by_cases hf : 3 ≤ j ∧ j ≤ 14
    · have hb : (Nat.ble 3 j && Nat.ble j 14) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq]; exact hf
      rw [hb, if_pos rfl, h.n1 (by omega), h.cur hj, h.prev (by omega) hj, pend,
        if_neg (by omega)]
      have := sched_step W (j - 3) (schedRec_Wt _ _)
      rw [show j - 3 + 1 = j + 1 - 3 by omega, show j - 3 + 3 = j by omega,
        show j - 3 + 2 = j - 1 by omega, show j - 3 + 4 = j + 1 by omega,
        show j - 3 = j + 1 - 4 by omega] at this
      exact this
    · have hb : (Nat.ble 3 j && Nat.ble j 14) = false := by
        rw [Bool.eq_false_iff]; intro hc; simp only [Bool.and_eq_true, Nat.ble_eq] at hc; omega
      rw [hb, if_neg (by simp), h.n1 (by omega), pend, if_pos (by omega)]
  · -- the previous schedule words
    intro _ hj1
    rw [show j + 1 + 3 = j + 4 by ring, show wreg (j + 4) = wreg j by unfold wreg; congr 1; omega,
      eo _ (wreg_ne_y0 _) (wreg_ne_y1 _) (wreg_ne_y2 _) (wreg_ne_y7 _) (wreg_ne _ _ (by omega))
        (wreg_ne _ _ (by omega)), h.cur hj, show j + 1 - 1 = j by omega]
  · -- the next group
    intro hj2
    rw [show j + 1 + 1 = j + 2 by ring, eo _ (wreg_ne_y0 _) (wreg_ne_y1 _) (wreg_ne_y2 _) (wreg_ne_y7 _)
      (wreg_ne _ _ (by omega)) (wreg_ne _ _ (by omega))]
    exact h.n2 (by omega)
  · -- the group after next
    intro hj3
    rw [show j + 1 + 2 = j + 3 by ring, ew3]
    by_cases hm : 1 ≤ j ∧ j ≤ 12
    · have hb : (Nat.ble 1 j && Nat.ble j 12) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq]; exact hm
      rw [hb, if_pos rfl, h.prev hm.1 hj, h.cur hj, pend, if_neg (by omega),
        show j + 3 - 4 = j - 1 by omega, show j + 3 - 3 = j by omega]
    · have hb : (Nat.ble 1 j && Nat.ble j 12) = false := by
        rw [Bool.eq_false_iff]; intro hc; simp only [Bool.and_eq_true, Nat.ble_eq] at hc; omega
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hb, if_neg (by simp), h.n3 rfl, pend, if_pos (by omega)]
  · intro h0; omega
  · rw [eo _ (by decide) (by decide) (by decide) (by decide) (wreg_ne_y8' _) (wreg_ne_y8' _)]; exact h.y8
  · rw [eo _ (by decide) (by decide) (by decide) (by decide) (wreg_ne_y9' _) (wreg_ne_y9' _)]; exact h.y9
  · rw [eo _ (by decide) (by decide) (by decide) (by decide) (wreg_ne_y10' _) (wreg_ne_y10' _)]; exact h.y10
  · rw [eg]; exact h.rsi
  · rw [eg]; exact h.rdx

theorem groups_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (s : State) (h : GroupInv G blk 0 s) :
    WP isa (.block groups) s (GroupInv G blk 16) := by
  have := WP.block_iter (M := isa) groupCode (GroupInv G blk) 0 16
    (fun i hi s hs => by simpa using group_ok G hwf blk i hi s (by simpa using hs)) s h
  simpa [groups] using this

/-! ## Loading the message block -/

/-- The invariant at the head of the per-block loop. -/
structure LoopInv (G : Ghost) (blk : Nat) (s : State) : Prop where
  frame : Frame G.s0 s
  y1 : s.getX .y1 = abef (initVars (G.Hb blk))
  y2 : s.getX .y2 = cdgh (initVars (G.Hb blk))
  y8 : s.getX .y8 = bswapX
  rsi : s.gpr.rsi = G.inp + BitVec.ofNat 64 (64 * blk)
  rdx : s.gpr.rdx = BitVec.ofNat 64 (G.n - blk)

theorem load_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) : WP isa (.block loadMsg) s (GroupInv G blk 0) := by
  have hp : ∀ k, k < 4 → InRegions (s.rd ++ s.wr) (s.gpr.rsi + BitVec.ofNat 64 (16 * k)) 16 := by
    intro k hk
    rw [h.rsi, h.frame.rd, add_ofNat_add]
    exact inRegions_of_mem hwf.hrdm (by simp only; have := hwf.hn; omega) _ _ (by simp only; omega)
  have hp0 := hp 0 (by decide); have hp1 := hp 1 (by decide); have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hp0 hp1 hp2 hp3
  obtain ⟨q, hq, e3, e4, e5, e6, e9, e10, eo, eg, em, erd, ewr, elb⟩ := loadMsg_exec s hp0 hp1 hp2 hp3
  refine WP.block_intro q hq ?_
  have hv : ∀ k, k < 4 → pshufb128 (s.mem.readW (s.gpr.rsi + BitVec.ofNat 64 (16 * k)) 128) (s.getX .y8) =
      packW (Wt (G.Mb blk)) k := by
    intro k hk; rw [h.rsi, h.frame.mem, h.y8, add_ofNat_add]; exact msg_vec G hwf blk hblk k hk
  have hv0 := hv 0 (by decide); have hv1 := hv 1 (by decide); have hv2 := hv 2 (by decide)
  have hv3 := hv 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hv0 hv1 hv2 hv3
  have ow : ∀ w, w ≠ .y3 → w ≠ .y4 → w ≠ .y5 → w ≠ .y6 → w ≠ .y9 → w ≠ .y10 → q.1.getX w = s.getX w := eo
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [em]; exact h.frame.mem
  · rw [erd]; exact h.frame.rd
  · rw [ewr]; exact h.frame.wr
  · rw [elb]; exact h.frame.labels
  · intro r h1 h2; rw [eg]; exact h.frame.gpr r h1 h2
  · rw [ow _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.y1, varsAt_zero]
  · rw [ow _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.y2, varsAt_zero]
  · intro _; simp only [wreg, Nat.zero_mod]; rw [e3, hv0]
  · intro h1; omega
  · intro _; simp only [wreg, Nat.zero_add, Nat.one_mod]; rw [e4, hv1, pend, if_pos (by decide)]
  · intro _; simp only [wreg, Nat.zero_add, Nat.reduceMod]; rw [e5, hv2, pend, if_pos (by decide)]
  · intro _; simp only [wreg, Nat.reduceMod]; rw [e6, hv3]
  · rw [ow _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.y8
  · rw [e9]; exact h.y1
  · rw [e10]; exact h.y2
  · rw [eg]; exact h.rsi
  · rw [eg]; exact h.rdx

/-! ## Adding the hash value -/

theorem Hb_succ (G : Ghost) (blk : Nat) :
    abef (initVars (G.Hb (blk + 1))) =
      padddX (abef (varsAt (G.Hb blk) (G.Mb blk) 64)) (abef (initVars (G.Hb blk))) ∧
    cdgh (initVars (G.Hb (blk + 1))) =
      padddX (cdgh (varsAt (G.Hb blk) (G.Mb blk) 64)) (cdgh (initVars (G.Hb blk))) := by
  rw [Ghost.Hb, stateAfter_succ, compress_eq, ← Ghost.Hb, ← Ghost.Mb]
  generalize varsAt (G.Hb blk) (G.Mb blk) 64 = v
  constructor <;>
    simp only [abef, cdgh, initVars, padddX_vec4, List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem ofNat_sub_one (a : Nat) (h1 : 1 ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1#64 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem finish_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : GroupInv G blk 16 s) :
    WP isa (.block finish) s (fun s' => LoopInv G (blk + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (G.n - (blk + 1)) == 0#64)) := by
  obtain ⟨q, hq, e1, e2, eo, eg, ez, em, erd, ewr, elb⟩ := finish_exec s
  refine WP.block_intro q hq ?_
  obtain ⟨ha, he⟩ := Hb_succ G blk
  have hrdx : s.gpr.rdx - 1#64 = BitVec.ofNat 64 (G.n - (blk + 1)) := by
    rw [h.rdx, ofNat_sub_one _ (by omega) (by have := hwf.hn; omega)]
    congr 1
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [em]; exact h.frame.mem
  · rw [erd]; exact h.frame.rd
  · rw [ewr]; exact h.frame.wr
  · rw [elb]; exact h.frame.labels
  · intro r h1 h2; rw [eg]
    have := h.frame.gpr r h1 h2
    cases r <;> first | exact this | exact absurd rfl h1 | exact absurd rfl h2
  · rw [e1, h.y1, h.y9, ha]
  · rw [e2, h.y2, h.y10, he]
  · rw [eo _ (by decide) (by decide)]; exact h.y8
  · rw [eg]; show s.gpr.rsi + 64#64 = _
    rw [h.rsi, show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, add_ofNat_add,
      show 64 * blk + 64 = 64 * (blk + 1) by ring]
  · rw [eg]; exact hrdx
  · rw [ez, hrdx]

theorem block_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) :
    WP isa (.block blockCode) s (fun s' => LoopInv G (blk + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (G.n - (blk + 1)) == 0#64)) := by
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (load_ok G hwf blk hblk s h) ?_
  intro s1 h1
  refine WP.mono (groups_ok G hwf blk s1 h1) ?_
  intro s2 h2
  exact finish_ok G hwf blk hblk s2 h2

/-! ## The loop -/

theorem loop_ok (G : Ghost) (hwf : G.WF) (s : State) (hn0 : 0 < G.n) (h : LoopInv G 0 s) :
    WP isa (.loop (.block blockCode) .ne) s (LoopInv G G.n) := by
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => 0 < m ∧ m ≤ G.n ∧ LoopInv G (G.n - m) s) ?_
    G.n s ⟨hn0, le_refl _, by simpa using h⟩
  rintro m s ⟨hm0, hmn, hinv⟩
  refine WP.mono (block_ok G hwf (G.n - m) (by omega) s hinv) ?_
  rintro s' ⟨hinv', hzf⟩
  have e : G.n - (G.n - m + 1) = m - 1 := by omega
  rw [e] at hzf
  have hm : m - 1 < 2 ^ 64 := by have := hwf.hn; omega
  by_cases hm1 : m = 1
  · subst hm1
    left
    refine ⟨by simp [evalCond, hzf], ?_⟩
    have : G.n - 1 + 1 = G.n := by omega
    rwa [this] at hinv'
  · right
    refine ⟨?_, m - 1, by omega, by omega, by omega, ?_⟩
    · simp only [evalCond, hzf, Option.map_some]
      congr 1
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp at this
      omega
    · have : G.n - m + 1 = G.n - (m - 1) := by omega
      rwa [this] at hinv'

end CC.X86.SHA256ShaNi
