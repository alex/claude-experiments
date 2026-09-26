import ClaudeCrypto.Arm.SHA256.CePhases
import ClaudeCrypto.Arm.SHA256.CeLemmas

/-!
# The AArch64 SHA-256 block function: one block

Composition of the phase lemmas with the arithmetic lemmas, instantiated
with the specification's values (`varsAt`, `Wt`).
-/

namespace CC.Arm.SHA256Ce

open CC.Spec.SHA256

/-! ## Frame -/

/-- The vector registers written by the function. -/
def touched : List VReg := [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v16, .v18, .v19]

theorem wreg_mem (k : Nat) : wreg k ∈ touched := by
  unfold wreg; split <;> decide

theorem wreg_mod (k j : Nat) : wreg (k % 4 + j) = wreg (k + j) := by
  unfold wreg; rw [show (k % 4 + j) % 4 = (k + j) % 4 by omega]

theorem wreg_eq_iff (a b : Nat) : wreg a = wreg b ↔ a % 4 = b % 4 := by
  unfold wreg
  constructor
  · intro h
    have ha := Nat.mod_lt a (show 4 > 0 by decide)
    have hb := Nat.mod_lt b (show 4 > 0 by decide)
    generalize a % 4 = x at *; generalize b % 4 = y at *
    interval_cases x <;> interval_cases y <;> simp_all
  · intro h; rw [h]

theorem wreg_ne_v0 (k : Nat) : wreg k ≠ .v0 := by unfold wreg; split <;> decide
theorem wreg_ne_v1 (k : Nat) : wreg k ≠ .v1 := by unfold wreg; split <;> decide
theorem wreg_ne_v2 (k : Nat) : wreg k ≠ .v2 := by unfold wreg; split <;> decide
theorem wreg_ne_v16 (k : Nat) : wreg k ≠ .v16 := by unfold wreg; split <;> decide
theorem wreg_ne_v18 (k : Nat) : wreg k ≠ .v18 := by unfold wreg; split <;> decide
theorem wreg_ne_v19 (k : Nat) : wreg k ≠ .v19 := by unfold wreg; split <;> decide

/-- `s` differs from `s0` only in the registers the function may clobber. -/
structure Frame (s0 s : State) : Prop where
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  sp : s.sp = s0.sp
  x : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s.getX r = s0.getX r
  v : ∀ r, r ∉ touched → s.getV r = s0.getV r

theorem Frame.refl (s : State) : Frame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.setV {s0 s : State} (h : Frame s0 s) (r : VReg) (hr : r ∈ touched) (x : BitVec 128) :
    Frame s0 (s.setV r x) :=
  ⟨h.mem, h.rd, h.wr, h.labels, h.sp, fun r' h1 h2 h3 => h.x r' h1 h2 h3, fun r' hr' => by
    rw [State.getV_setV_ne _ _ _ _ (fun e => hr' (by rw [e]; exact hr))]; exact h.v r' hr'⟩

theorem Frame.setX {s0 s : State} (h : Frame s0 s) (r : XReg) (hr : r = .x1 ∨ r = .x2 ∨ r = .x3)
    (x : BitVec 64) : Frame s0 (s.setX r x) :=
  ⟨h.mem, h.rd, h.wr, h.labels, h.sp, fun r' h1 h2 h3 => by
    rw [State.getX_setX_ne _ _ _ _ (by rcases hr with rfl | rfl | rfl <;> assumption)]
    exact h.x r' h1 h2 h3, fun r' hr' => h.v r' hr'⟩

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
def st : Addr := G.s0.getX .x0
def inp : Addr := G.s0.getX .x1
def kb : Addr := G.s0.labels kLabel
def Hb (blk : Nat) : List Word := stateAfter G.H G.msg blk
def Mb (blk : Nat) : List Word := msgBlock G.msg blk
end Ghost

/-- The preconditions relevant to the loop. -/
structure Ghost.WF (G : Ghost) : Prop where
  hlen : G.msg.length = 64 * G.n
  hn : 64 * G.n < 2 ^ 64
  hmsg : ∀ i < 64 * G.n, G.s0.mem (G.inp + BitVec.ofNat 64 i) = G.msg[i]!
  hK : ∀ i < 64, G.s0.mem.readW (G.kb + BitVec.ofNat 64 (4 * i)) 32 = K[i]!
  hrdm : ⟨G.inp, 64 * G.n⟩ ∈ G.s0.rd
  hrdK : ⟨G.kb, 256⟩ ∈ G.s0.rd

/-! ## Address arithmetic and memory facts -/

theorem add_ofNat_add (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem inRegions_of_mem {rs rs' : List Region} {r : Region} (h : r ∈ rs) (hl : r.len < 2 ^ 64)
    (k n : Nat) (hk : k + n ≤ r.len) : InRegions (rs ++ rs') (r.base + BitVec.ofNat 64 k) n :=
  ⟨r, List.mem_append_left _ h, Region.contains_offset _ _ _ _ hk hl⟩

/-- Word `i` of the round-constant table, four at a time. -/
theorem K_vec (G : Ghost) (hwf : G.WF) (j : Nat) (hj : j < 16) :
    G.s0.mem.readW (G.kb + BitVec.ofNat 64 (16 * j)) 128 =
      vec4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
  rw [readW_128]
  have e : ∀ c : Nat, c < 4 → G.kb + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (4 * c) =
      G.kb + BitVec.ofNat 64 (4 * (4 * j + c)) := fun c _ => by
    rw [add_ofNat_add]; congr 2; ring
  have e1 := e 1 (by decide); have e2 := e 2 (by decide); have e3 := e 3 (by decide)
  simp only [Nat.reduceMul] at e1 e2 e3
  rw [e1, e2, e3, show 16 * j = 4 * (4 * j + 0) by ring, hwf.hK _ (by omega), hwf.hK _ (by omega),
    hwf.hK _ (by omega), hwf.hK _ (by omega), Nat.add_zero]

/-- Four rounds of the specification. -/
theorem varsAt_four (H M : List Word) (hM : M.length = 16) (j : Nat) (hj : j < 16) :
    varsAt H M (4 * (j + 1)) =
      round (round (round (round (varsAt H M (4 * j)) K[4 * j]! (Wt M (4 * j))) K[4 * j + 1]!
        (Wt M (4 * j + 1))) K[4 * j + 2]! (Wt M (4 * j + 2))) K[4 * j + 3]! (Wt M (4 * j + 3)) := by
  rw [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, varsAt_succ _ _ hM _ (by omega),
    varsAt_succ _ _ hM _ (by omega), varsAt_succ _ _ hM _ (by omega), varsAt_succ _ _ hM _ (by omega)]

theorem schedRec_Wt (M : List Word) (j : Nat) : SchedRec (Wt M) j := by
  intro t h1 _; exact Wt_ge M t (by omega)

/-! ## Four rounds -/

/-- The invariant before group `j` (rounds `4j .. 4j+3`) of block `blk`. -/
structure GroupInv (G : Ghost) (blk j : Nat) (s : State) : Prop where
  frame : Frame G.s0 s
  v0 : s.getV .v0 = abcd (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
  v1 : s.getV .v1 = efgh (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
  w : ∀ i < 4, j + i < 16 → s.getV (wreg (j + i)) = packW (Wt (G.Mb blk)) (j + i)
  v18 : s.getV .v18 = abcd (initVars (G.Hb blk))
  v19 : s.getV .v19 = efgh (initVars (G.Hb blk))
  x1 : s.getX .x1 = G.inp + BitVec.ofNat 64 (64 * (blk + 1))
  x2 : s.getX .x2 = BitVec.ofNat 64 (G.n - blk)
  x3 : s.getX .x3 = G.kb

theorem groupPost_frame (p off : Nat) (sched : Bool) (s0 s : State) (h : Frame s0 s) :
    Frame s0 (groupPost p off sched s) := by
  unfold groupPost
  exact ((((h.setV _ (by decide) _).setV _ (wreg_mem _) _).setV _ (by decide) _).setV _ (by decide) _).setV
    _ (by decide) _

theorem group_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (j : Nat) (hj : j < 16) (s : State)
    (h : GroupInv G blk j s) : WP isa (.block (groupCode j)) s (GroupInv G blk (j + 1)) := by
  have hM : (G.Mb blk).length = 16 := msgBlock_length _ _
  have hperm : InRegions (s.rd ++ s.wr) (s.getX .x3 + BitVec.ofNat 64 (16 * j)) 16 := by
    rw [h.x3, h.frame.rd]
    exact inRegions_of_mem hwf.hrdK (by norm_num) _ _ (by simp only; omega)
  obtain ⟨t, ht⟩ := group_exec (j % 4) (Nat.mod_lt _ (by decide)) (16 * j) (Nat.blt j 12) s hperm
  refine WP.block_intro _ ht ?_
  have hW : ∀ i < 4, j + i < 16 → s.getV (wreg (j % 4 + i)) = packW (Wt (G.Mb blk)) (j + i) := by
    intro i hi hji; rw [wreg_mod]; exact h.w i hi hji
  have hW0 := hW 0 (by decide) (by omega)
  simp only [Nat.add_zero] at hW0
  have hK : s.mem.readW (s.getX .x3 + BitVec.ofNat 64 (16 * j)) 128 =
      vec4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
    rw [h.x3, h.frame.mem]; exact K_vec G hwf j hj
  have hround : hw4 (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
      (vadd32 (s.mem.readW (s.getX .x3 + BitVec.ofNat 64 (16 * j)) 128) (s.getV (wreg (j % 4)))) =
      varsAt (G.Hb blk) (G.Mb blk) (4 * (j + 1)) := by
    rw [hK, hW0, packW, hw4_eq, varsAt_four _ _ hM j hj]
  have hs := h.frame
  refine ⟨groupPost_frame _ _ _ _ _ h.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- a, b, c, d
    simp only [groupPost, State.getV_setV, reduceCtorEq, ite_true, ite_false, h.v0, h.v1,
      sha256h_vars, hround]
  · -- e, f, g, h
    simp only [groupPost, State.getV_setV, reduceCtorEq, ite_true, ite_false, h.v0, h.v1,
      sha256h2_vars, hround]
  · -- the message schedule
    intro i hi hji
    simp only [groupPost, State.getV_setV, wreg_ne_v0, wreg_ne_v1, wreg_ne_v2, wreg_ne_v16, ite_false]
    by_cases h3 : i = 3
    · subst h3
      have hs : Nat.blt j 12 = true := by simp only [Nat.blt_eq]; omega
      rw [if_pos ((wreg_eq_iff _ _).mpr (by omega)), hs, if_pos rfl,
        hW0, hW 1 (by decide) (by omega), hW 2 (by decide) (by omega), hW 3 (by decide) (by omega),
        sched_step _ _ (schedRec_Wt _ _)]
    · rw [if_neg (fun e => by have := (wreg_eq_iff _ _).mp e; omega)]
      rw [show j + 1 + i = j + (i + 1) by omega]
      exact h.w (i + 1) (by omega) (by omega)
  · simp only [groupPost, State.getV_setV, reduceCtorEq, ite_false,
      show (VReg.v18 = wreg (j % 4)) = False from propext ⟨fun e => wreg_ne_v18 _ e.symm, False.elim⟩]
    exact h.v18
  · simp only [groupPost, State.getV_setV, reduceCtorEq, ite_false,
      show (VReg.v19 = wreg (j % 4)) = False from propext ⟨fun e => wreg_ne_v19 _ e.symm, False.elim⟩]
    exact h.v19
  · exact (show (groupPost _ _ _ s).getX .x1 = s.getX .x1 from rfl).trans h.x1
  · exact (show (groupPost _ _ _ s).getX .x2 = s.getX .x2 from rfl).trans h.x2
  · exact (show (groupPost _ _ _ s).getX .x3 = s.getX .x3 from rfl).trans h.x3

theorem groups_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (s : State) (h : GroupInv G blk 0 s) :
    WP isa (.block groups) s (GroupInv G blk 16) := by
  have := WP.block_iter (M := isa) groupCode (GroupInv G blk) 0 16
    (fun i hi s hs => by simpa using group_ok G hwf blk i hi s (by simpa using hs)) s h
  simpa [groups] using this

/-! ## Loading the message block -/

/-- The invariant at the head of the per-block loop. -/
structure LoopInv (G : Ghost) (blk : Nat) (s : State) : Prop where
  frame : Frame G.s0 s
  v0 : s.getV .v0 = abcd (initVars (G.Hb blk))
  v1 : s.getV .v1 = efgh (initVars (G.Hb blk))
  x1 : s.getX .x1 = G.inp + BitVec.ofNat 64 (64 * blk)
  x2 : s.getX .x2 = BitVec.ofNat 64 (G.n - blk)
  x3 : s.getX .x3 = G.kb

theorem msg_byte_addr (a : Addr) (x : Nat) (c : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 c = a + BitVec.ofNat 64 (x + c) := add_ofNat_add a x c

/-- A message word, loaded little-endian and byte-reversed. -/
theorem msg_word (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (w : Nat) (hw : w < 16) :
    rev8in32 (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 4 * w)) 32) = msgWord G.msg blk w := by
  rw [rev8in32_readW]
  have e : ∀ c : Nat, G.inp + BitVec.ofNat 64 (64 * blk + 4 * w) + BitVec.ofNat 64 c =
      G.inp + BitVec.ofNat 64 (64 * blk + 4 * w + c) := fun c => add_ofNat_add _ _ _
  have e1 := e 1; have e2 := e 2; have e3 := e 3
  rw [show BitVec.ofNat 64 1 = (1 : BitVec 64) from rfl] at e1
  rw [show BitVec.ofNat 64 2 = (2 : BitVec 64) from rfl] at e2
  rw [show BitVec.ofNat 64 3 = (3 : BitVec 64) from rfl] at e3
  rw [e1, e2, e3, msgWord, wordBE, hwf.hmsg _ (by omega), hwf.hmsg _ (by omega),
    hwf.hmsg _ (by omega), hwf.hmsg _ (by omega)]

/-- Four message words, as loaded by `ld1` + `rev32`. -/
theorem msg_vec (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (k : Nat) (hk : k < 4) :
    rev32 (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (16 * k)) 128) =
      packW (Wt (G.Mb blk)) k := by
  rw [readW_128, rev32_vec4]
  have e : ∀ c : Nat, c < 4 → G.inp + BitVec.ofNat 64 (64 * blk) + BitVec.ofNat 64 (16 * k) +
      BitVec.ofNat 64 (4 * c) = G.inp + BitVec.ofNat 64 (64 * blk + 4 * (4 * k + c)) := fun c _ => by
    rw [add_ofNat_add, add_ofNat_add]; congr 2; ring
  have e1 := e 1 (by decide); have e2 := e 2 (by decide); have e3 := e 3 (by decide)
  have e0 := e 0 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at e0 e1 e2 e3
  have hM : ∀ c, c < 4 → Wt (G.Mb blk) (4 * k + c) = msgWord G.msg blk (4 * k + c) := fun c _ => by
    rw [Wt_lt _ _ (by omega), Ghost.Mb, msgBlock_getElem _ _ _ (by omega)]
  have hM0 : Wt (G.Mb blk) (4 * k) = msgWord G.msg blk (4 * k) := hM 0 (by decide)
  rw [e1, e2, e3, e0, msg_word G hwf blk hblk _ (by omega), msg_word G hwf blk hblk _ (by omega),
    msg_word G hwf blk hblk _ (by omega), msg_word G hwf blk hblk _ (by omega), packW,
    hM0, hM 1 (by decide), hM 2 (by decide), hM 3 (by decide), Nat.add_zero]

theorem load_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) : WP isa (.block loadMsg) s (GroupInv G blk 0) := by
  have hp : ∀ k, k < 4 → InRegions (s.rd ++ s.wr) (s.getX .x1 + BitVec.ofNat 64 (16 * k)) 16 := by
    intro k hk
    rw [h.x1, h.frame.rd, msg_byte_addr]
    exact inRegions_of_mem hwf.hrdm (by simp only; have := hwf.hn; omega) _ _ (by simp only; omega)
  have hp0 := hp 0 (by decide); have hp1 := hp 1 (by decide); have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hp0 hp1 hp2 hp3
  obtain ⟨t, ht⟩ := loadMsg_exec s hp0 hp1 hp2 hp3
  refine WP.block_intro _ ht ?_
  have hv : ∀ k, k < 4 → rev32 (s.mem.readW (s.getX .x1 + BitVec.ofNat 64 (16 * k)) 128) =
      packW (Wt (G.Mb blk)) k := by
    intro k hk; rw [h.x1, h.frame.mem]; exact msg_vec G hwf blk hblk k hk
  have hv0 := hv 0 (by decide); have hv1 := hv 1 (by decide); have hv2 := hv 2 (by decide)
  have hv3 := hv 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hv0 hv1 hv2 hv3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold loadMsgPost
    exact (((((((h.frame.setV _ (by decide) _).setV _ (by decide) _).setV _ (by decide) _).setV _
      (by decide) _).setX _ (by simp) _).setV _ (by decide) _).setV _ (by decide) _)
  · simp only [loadMsgPost, State.getV_setV, reduceCtorEq, ite_false, State.setX_getV]
    exact h.v0
  · simp only [loadMsgPost, State.getV_setV, reduceCtorEq, ite_false, State.setX_getV]
    exact h.v1
  · intro i hi _
    simp only [Nat.zero_add]
    interval_cases i <;>
      simp only [loadMsgPost, wreg, Nat.reduceMod, State.getV_setV, reduceCtorEq, ite_false, ite_true,
        State.setX_getV, hv0, hv1, hv2, hv3]
  · simp only [loadMsgPost, State.getV_setV, reduceCtorEq, ite_false, ite_true, State.setX_getV]
    exact h.v0
  · simp only [loadMsgPost, State.getV_setV, reduceCtorEq, ite_false, ite_true, State.setX_getV]
    exact h.v1
  · refine (show (loadMsgPost s).getX .x1 = s.getX .x1 + BitVec.ofNat 64 64 from rfl).trans ?_
    rw [h.x1, add_ofNat_add, show 64 * blk + 64 = 64 * (blk + 1) by ring]
  · exact (show (loadMsgPost s).getX .x2 = s.getX .x2 from rfl).trans h.x2
  · exact (show (loadMsgPost s).getX .x3 = s.getX .x3 from rfl).trans h.x3

/-! ## Adding the hash value -/

theorem Hb_succ (G : Ghost) (blk : Nat) :
    abcd (initVars (G.Hb (blk + 1))) =
      vadd32 (abcd (varsAt (G.Hb blk) (G.Mb blk) 64)) (abcd (initVars (G.Hb blk))) ∧
    efgh (initVars (G.Hb (blk + 1))) =
      vadd32 (efgh (varsAt (G.Hb blk) (G.Mb blk) 64)) (efgh (initVars (G.Hb blk))) := by
  rw [Ghost.Hb, stateAfter_succ, compress_eq, ← Ghost.Hb, ← Ghost.Mb]
  generalize varsAt (G.Hb blk) (G.Mb blk) 64 = v
  constructor <;>
    simp only [abcd, efgh, initVars, vadd32_vec4, List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem ofNat_sub_one (a : Nat) (h1 : 1 ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1#64 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem finish_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : GroupInv G blk 16 s) : WP isa (.block finish) s (LoopInv G (blk + 1)) := by
  obtain ⟨t, ht⟩ := finish_exec s
  refine WP.block_intro _ ht ?_
  obtain ⟨ha, he⟩ := Hb_succ G blk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finishPost
    exact ((h.frame.setV _ (by decide) _).setV _ (by decide) _).setX _ (by simp) _
  · have hv0 := h.v0; rw [show 4 * 16 = 64 from rfl] at hv0
    refine (show (finishPost s).getV .v0 = vadd32 (s.getV .v0) (s.getV .v18) from rfl).trans ?_
    rw [hv0, h.v18, ha]
  · have hv1 := h.v1; rw [show 4 * 16 = 64 from rfl] at hv1
    refine (show (finishPost s).getV .v1 = vadd32 (s.getV .v1) (s.getV .v19) from rfl).trans ?_
    rw [hv1, h.v19, he]
  · exact (show (finishPost s).getX .x1 = s.getX .x1 from rfl).trans h.x1
  · refine (show (finishPost s).getX .x2 = s.getX .x2 - 1#64 from rfl).trans ?_
    rw [h.x2, ofNat_sub_one _ (by omega) (by have := hwf.hn; omega), show G.n - blk - 1 = G.n - (blk + 1) by omega]
  · exact (show (finishPost s).getX .x3 = s.getX .x3 from rfl).trans h.x3

theorem block_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) : WP isa (.block blockCode) s (LoopInv G (blk + 1)) := by
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (load_ok G hwf blk hblk s h) ?_
  intro s1 h1
  refine WP.mono (groups_ok G hwf blk s1 h1) ?_
  intro s2 h2
  exact finish_ok G hwf blk hblk s2 h2

/-! ## The loop -/

theorem loop_ok (G : Ghost) (hwf : G.WF) (s : State) (hn0 : 0 < G.n) (h : LoopInv G 0 s) :
    WP isa (.loop (.block blockCode) (.cbnz .x2)) s (LoopInv G G.n) := by
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => 0 < m ∧ m ≤ G.n ∧ LoopInv G (G.n - m) s) ?_
    G.n s ⟨hn0, le_refl _, by simpa using h⟩
  rintro m s ⟨hm0, hmn, hinv⟩
  refine WP.mono (block_ok G hwf (G.n - m) (by omega) s hinv) ?_
  intro s' hinv'
  have hx2 := hinv'.x2
  have e : G.n - (G.n - m + 1) = m - 1 := by omega
  rw [e] at hx2
  have hm : m - 1 < 2 ^ 64 := by have := hwf.hn; omega
  by_cases hm1 : m = 1
  · subst hm1
    left
    refine ⟨by simp [isa, evalCond, hx2], ?_⟩
    have : G.n - 1 + 1 = G.n := by omega
    rwa [this] at hinv'
  · right
    refine ⟨?_, m - 1, by omega, by omega, by omega, ?_⟩
    · simp only [isa, evalCond, hx2, Option.some.injEq]
      simp only [bne_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      simp [Nat.mod_eq_of_lt hm] at this
      omega
    · have : G.n - m + 1 = G.n - (m - 1) := by omega
      rwa [this] at hinv'

end CC.Arm.SHA256Ce
