import ClaudeCrypto.Ppc.SHA256.P8Step

/-!
# The ppc64le SHA-256 block function: four rounds

Frame, ghost state and invariants; composition of the group-head and step
lemmas into one group of four rounds, instantiated with the specification's
values (`varsAt`, `Wt`).
-/

namespace CC.Ppc.SHA256P8

open CC.Spec.SHA256

set_option linter.unusedSimpArgs false

/-! ## Frame -/

/-- The GPRs written by the function. -/
def clobG : GReg → Bool
  | .r0 | .r4 | .r5 | .r6 | .r7 | .r8 | .r9 | .r10 | .r11 | .r12 => true
  | _ => false

/-- `s` differs from `s0` only in the registers the function may clobber (and CR0). -/
structure Frame (s0 s : State) : Prop where
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  lr : s.lr = s0.lr
  vsr : s.vsr = s0.vsr
  cr1to7 : s.cr1to7 = s0.cr1to7
  g : ∀ r, clobG r = false → s.getG r = s0.getG r
  v : ∀ r, r.nonvolatile = true → s.getV r = s0.getV r

theorem Frame.refl (s : State) : Frame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.setV {s0 s : State} (h : Frame s0 s) (r : VReg) (hr : r.nonvolatile = false)
    (x : BitVec 128) : Frame s0 (s.setV r x) :=
  ⟨h.mem, h.rd, h.wr, h.labels, h.lr, h.vsr, h.cr1to7, h.g, fun r' hr' => by
    rw [State.getV_setV_ne _ _ _ _ (fun e => by subst e; rw [hr] at hr'; cases hr')]; exact h.v r' hr'⟩

theorem Frame.setG {s0 s : State} (h : Frame s0 s) (r : GReg) (hr : clobG r = true)
    (x : BitVec 64) : Frame s0 (s.setG r x) :=
  ⟨h.mem, h.rd, h.wr, h.labels, h.lr, h.vsr, h.cr1to7, fun r' hr' => by
    rw [State.getG_setG_ne _ _ _ _ (fun e => by subst e; rw [hr] at hr'; cases hr')]; exact h.g r' hr',
    h.v⟩

theorem Frame.same {s0 s s' : State} (h : Frame s0 s) (hs : Same s s')
    (hv : ∀ r, r.nonvolatile = true → s'.getV r = s.getV r) : Frame s0 s' :=
  ⟨hs.mem.trans h.mem, hs.rd.trans h.rd, hs.wr.trans h.wr, hs.labels.trans h.labels, hs.lr.trans h.lr,
    hs.vsr.trans h.vsr, hs.cr1to7.trans h.cr1to7,
    fun r hr => (show s'.getG r = s.getG r from congrArg (GRegs.get · r) hs.g).trans (h.g r hr),
    fun r hr => (hv r hr).trans (h.v r hr)⟩

theorem stepTouched_nonvolatile (x : VReg) (h : x.nonvolatile = true) : stepTouched x = false := by
  cases x <;> first | rfl | cases h

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
def st : Addr := G.s0.getG .r3
def inp : Addr := G.s0.getG .r4
def kb : Addr := G.s0.labels kLabel
def Hb (blk : Nat) : List Word := stateAfter G.H G.msg blk
def Mb (blk : Nat) : List Word := msgBlock G.msg blk
end Ghost

/-- The preconditions relevant to the loop. -/
structure Ghost.WF (G : Ghost) : Prop where
  hlen : G.msg.length = 64 * G.n
  hn : 64 * G.n < 2 ^ 64
  hmsg : ∀ i < 64 * G.n, G.s0.mem (G.inp + BitVec.ofNat 64 i) = G.msg[i]!
  hK : ∀ i < 68, G.s0.mem.readW (G.kb + BitVec.ofNat 64 (4 * i)) 32 = table[i]!
  hrdm : ⟨G.inp, 64 * G.n⟩ ∈ G.s0.rd
  hrdK : ⟨G.kb, 272⟩ ∈ G.s0.rd

/-- The registers that are constant throughout the loop. -/
structure Consts (G : Ghost) (s : State) : Prop where
  frame : Frame G.s0 s
  r6 : s.getG .r6 = G.kb
  r10 : s.getG .r10 = G.kb + 64#64
  r11 : s.getG .r11 = G.kb + 128#64
  r12 : s.getG .r12 = G.kb + 192#64
  r7 : s.getG .r7 = 16#64
  r8 : s.getG .r8 = 32#64
  r9 : s.getG .r9 = 48#64
  v18 : s.getV .v18 = 0
  v19 : s.getV .v19 = bswapVec

theorem Consts.same {G : Ghost} {s s' : State} (h : Consts G s) (hs : Same s s')
    (hv : ∀ r, r.nonvolatile = true ∨ r = .v18 ∨ r = .v19 → s'.getV r = s.getV r) : Consts G s' := by
  have hg : ∀ r, s'.getG r = s.getG r := fun r => congrArg (GRegs.get · r) hs.g
  exact ⟨h.frame.same hs (fun r hr => hv r (Or.inl hr)), (hg _).trans h.r6, (hg _).trans h.r10,
    (hg _).trans h.r11, (hg _).trans h.r12, (hg _).trans h.r7, (hg _).trans h.r8, (hg _).trans h.r9,
    (hv _ (Or.inr (Or.inl rfl))).trans h.v18, (hv _ (Or.inr (Or.inr rfl))).trans h.v19⟩

theorem Consts.step {G : Ghost} {s : State} (h : Consts G s) (r : Nat) (hr : r < 8) :
    Consts G (stepPost r s) :=
  h.same (stepPost_same r s) fun x hx => stepPost_getV r hr s x (by
    rcases hx with hx | rfl | rfl
    · exact stepTouched_nonvolatile x hx
    · rfl
    · rfl)

/-- The hash value, packed: (a, b, c, d) and (e, f, g, h). -/
def hv0 (H : List Word) : BitVec 128 := w4 H[0]! H[1]! H[2]! H[3]!
def hv1 (H : List Word) : BitVec 128 := w4 H[4]! H[5]! H[6]! H[7]!

/-- The invariant before group `j` (rounds `4j .. 4j+3`) of block `blk`. -/
structure GroupInv (G : Ghost) (blk j : Nat) (s : State) : Prop where
  consts : Consts G s
  vars : VarsAt s (4 * j) (varsAt (G.Hb blk) (G.Mb blk) (4 * j))
  w : ∀ i < 4, j + i < 16 → s.getV (wreg (j + i)) = packW (Wt (G.Mb blk)) (j + i)
  v16 : s.getV .v16 = hv0 (G.Hb blk)
  v17 : s.getV .v17 = hv1 (G.Hb blk)
  r4 : s.getG .r4 = G.inp + BitVec.ofNat 64 (64 * (blk + 1))
  r5 : s.getG .r5 = -BitVec.ofNat 64 (G.n - blk)

/-! ## Address arithmetic and memory facts -/

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem add_ofNat_add (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem inRegions_of_mem {rs rs' : List Region} {r : Region} (h : r ∈ rs) (hl : r.len < 2 ^ 64)
    (k n : Nat) (hk : k + n ≤ r.len) : InRegions (rs ++ rs') (r.base + BitVec.ofNat 64 k) n :=
  ⟨r, List.mem_append_left _ h, Region.contains_offset _ _ _ _ hk hl⟩

theorem kRegs_ea (G : Ghost) (s : State) (h : Consts G s) (j : Nat) (hj : j < 16) :
    s.ea (kRegs j).1 (kRegs j).2 = G.kb + BitVec.ofNat 64 (16 * j) := by
  interval_cases j <;>
    simp only [kRegs, State.ea, State.raOr0, h.r6, h.r7, h.r8, h.r9, h.r10, h.r11, h.r12,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, zero_add, BitVec.add_zero, BitVec.add_assoc] <;>
    rfl

theorem table_K (i : Nat) (hi : i < 64) : table[i]! = K[i]! := by
  interval_cases i <;> rfl

theorem table_mask : [table[64]!, table[65]!, table[66]!, table[67]!] = bswapMask := rfl

/-- Words of the round-constant table, four at a time. -/
theorem K_vec (G : Ghost) (hwf : G.WF) (j : Nat) (hj : j < 16) :
    lxv G.s0.mem (G.kb + BitVec.ofNat 64 (16 * j)) = w4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
  have e : ∀ c : Nat, G.kb + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (4 * c) =
      G.kb + BitVec.ofNat 64 (4 * (4 * j + c)) := fun c => by
    rw [add_ofNat_add]; congr 2; ring
  have e1 : G.kb + BitVec.ofNat 64 (16 * j) + 4 = G.kb + BitVec.ofNat 64 (4 * (4 * j + 1)) := e 1
  have e2 : G.kb + BitVec.ofNat 64 (16 * j) + 8 = G.kb + BitVec.ofNat 64 (4 * (4 * j + 2)) := e 2
  have e3 : G.kb + BitVec.ofNat 64 (16 * j) + 12 = G.kb + BitVec.ofNat 64 (4 * (4 * j + 3)) := e 3
  simp only [lxv, w4]
  rw [e1, e2, e3, show 16 * j = 4 * (4 * j + 0) by ring, hwf.hK _ (by omega), hwf.hK _ (by omega),
    hwf.hK _ (by omega), hwf.hK _ (by omega), table_K _ (by omega), table_K _ (by omega),
    table_K _ (by omega), table_K _ (by omega)]
  simp only [Nat.add_zero]

/-- Four rounds of the specification. -/
theorem varsAt_four (H M : List Word) (hM : M.length = 16) (j : Nat) (hj : j < 16) :
    varsAt H M (4 * (j + 1)) =
      round (round (round (round (varsAt H M (4 * j)) K[4 * j]! (Wt M (4 * j))) K[4 * j + 1]!
        (Wt M (4 * j + 1))) K[4 * j + 2]! (Wt M (4 * j + 2))) K[4 * j + 3]! (Wt M (4 * j + 3)) := by
  rw [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, varsAt_succ _ _ hM _ (by omega),
    varsAt_succ _ _ hM _ (by omega), varsAt_succ _ _ hM _ (by omega), varsAt_succ _ _ hM _ (by omega)]

theorem schedRec_Wt (M : List Word) (j : Nat) : SchedRec (Wt M) j := by
  intro t h1 _; exact Wt_ge M t (by omega)

/-! ## The group head -/

/-- The vector registers written by `headCode`. -/
def headTouched : VReg → Bool
  | .v8 | .v9 | .v10 | .v11 | .v12 | .v14 => true
  | _ => false

theorem wreg_touched (k : Nat) : headTouched (wreg k) = true := by
  unfold wreg; split <;> rfl

theorem headPost_same (p : Nat) (ra rb : GReg) (sched : Bool) (s : State) :
    Same s (headPost p ra rb sched s) := by
  unfold headPost
  cases sched
  · exact ((Same.refl s).setV' _ _).setV' _ _
  · exact ((((Same.refl s).setV' _ _).setV' _ _).setV' _ _).setV' _ _

theorem headPost_getV (p : Nat) (ra rb : GReg) (sched : Bool) (s : State) (x : VReg)
    (hx : headTouched x = false) : (headPost p ra rb sched s).getV x = s.getV x := by
  have hw : wreg p ≠ x := fun e => by rw [← e, wreg_touched] at hx; cases hx
  have h12 : x ≠ .v12 := fun e => by subst e; cases hx
  have h14 : x ≠ .v14 := fun e => by subst e; cases hx
  unfold headPost
  cases sched <;> simp only [State.getV_setV, h12, h14, hw.symm, ite_false, ite_true,
    Bool.false_eq_true]

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

theorem wreg_ne_v12 (k : Nat) : wreg k ≠ .v12 := by unfold wreg; split <;> decide
theorem wreg_ne_v14 (k : Nat) : wreg k ≠ .v14 := by unfold wreg; split <;> decide

/-- What the group head computes. -/
theorem head_facts (G : Ghost) (hwf : G.WF) (blk j : Nat) (hj : j < 16) (s : State)
    (h : GroupInv G blk j s) :
    let s1 := headPost (j % 4) (kRegs j).1 (kRegs j).2 (Nat.blt j 12) s
    (∀ i < 4, word (s1.getV .v12) i = K[4 * j + i]! + Wt (G.Mb blk) (4 * j + i)) ∧
    (∀ i < 4, j + 1 + i < 16 → s1.getV (wreg (j + 1 + i)) = packW (Wt (G.Mb blk)) (j + 1 + i)) := by
  intro s1
  have hW : ∀ i < 4, j + i < 16 → s.getV (wreg (j % 4 + i)) = packW (Wt (G.Mb blk)) (j + i) := by
    intro i hi hji; rw [wreg_mod]; exact h.w i hi hji
  have hW0 := hW 0 (by decide) (by omega)
  simp only [Nat.add_zero] at hW0
  have hkv : lxv s.mem (s.ea (kRegs j).1 (kRegs j).2) =
      w4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]! := by
    rw [kRegs_ea G s h.consts j hj, h.consts.frame.mem]; exact K_vec G hwf j hj
  have hv12 : s1.getV .v12 = vadduwm (packW (Wt (G.Mb blk)) j)
      (w4 K[4 * j]! K[4 * j + 1]! K[4 * j + 2]! K[4 * j + 3]!) := by
    simp only [s1, headPost]
    cases Nat.blt j 12 <;>
      simp only [State.getV_setV, (wreg_ne_v12 _).symm, reduceCtorEq, ite_true, ite_false,
        Bool.false_eq_true, hkv, hW0]
  refine ⟨fun i hi => ?_, fun i hi hji => ?_⟩
  · rw [hv12, packW, vadduwm_w4]
    interval_cases i <;>
      simp only [word_w4_0, word_w4_1, word_w4_2, word_w4_3, Nat.add_zero, BitVec.add_comm]
  · by_cases h3 : i = 3
    · subst h3
      have hs : Nat.blt j 12 = true := by simp only [Nat.blt_eq]; omega
      simp only [s1, headPost, hs, ite_true]
      rw [State.getV_setV, if_pos ((wreg_eq_iff _ _).mpr (by omega)),
        hW0, hW 1 (by decide) (by omega), hW 2 (by decide) (by omega), hW 3 (by decide) (by omega),
        h.consts.v18, sched_step _ _ (schedRec_Wt _ _)]
    · have hne : wreg (j + 1 + i) ≠ wreg (j % 4) := fun e => by
        have := (wreg_eq_iff _ _).mp e; omega
      have : s1.getV (wreg (j + 1 + i)) = s.getV (wreg (j + 1 + i)) := by
        simp only [s1, headPost]
        cases Nat.blt j 12 <;>
          simp only [State.getV_setV, wreg_ne_v12, wreg_ne_v14, hne, ite_false, ite_true,
            Bool.false_eq_true]
      rw [this, show j + 1 + i = j + (i + 1) by omega]
      exact h.w (i + 1) (by omega) (by omega)

/-! ## One group -/

/-- The state after `groupCode j`. -/
def groupPost (j : Nat) (s : State) : State :=
  let q := 4 * (j % 2)
  stepPost (q + 3) (stepPost (q + 2) (stepPost (q + 1) (stepPost q
    (headPost (j % 4) (kRegs j).1 (kRegs j).2 (Nat.blt j 12) s))))

theorem exec_append {l₁ l₂ : List Instr} {s s₁ s₂ : State} {t₁ t₂ : List Leak}
    (h₁ : execBlock isa l₁ s = some (s₁, t₁)) (h₂ : execBlock isa l₂ s₁ = some (s₂, t₂)) :
    execBlock isa (l₁ ++ l₂) s = some (s₂, t₁ ++ t₂) := by
  rw [execBlock_append, h₁]; simp [h₂]

theorem group_exec (j : Nat) (s : State) (hperm : InRegions (s.rd ++ s.wr) (s.ea (kRegs j).1 (kRegs j).2) 16) :
    ∃ t, execBlock isa (groupCode j) s = some (groupPost j s, t) := by
  obtain ⟨t0, h0⟩ := head_exec (j % 4) (Nat.mod_lt _ (by decide)) _ _ (Nat.blt j 12) s hperm
  have hq : 4 * (j % 2) < 5 := by omega
  obtain ⟨t1, h1⟩ := step_exec (4 * (j % 2)) (by omega) (headPost (j % 4) (kRegs j).1 (kRegs j).2 (Nat.blt j 12) s)
  obtain ⟨t2, h2⟩ := step_exec (4 * (j % 2) + 1) (by omega) _
  obtain ⟨t3, h3⟩ := step_exec (4 * (j % 2) + 2) (by omega) _
  obtain ⟨t4, h4⟩ := step_exec (4 * (j % 2) + 3) (by omega) _
  exact ⟨_, exec_append (exec_append (exec_append (exec_append h0 h1) h2) h3) h4⟩

theorem group_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (j : Nat) (hj : j < 16) (s : State)
    (h : GroupInv G blk j s) : WP isa (.block (groupCode j)) s (GroupInv G blk (j + 1)) := by
  have hM : (G.Mb blk).length = 16 := msgBlock_length _ _
  have hperm : InRegions (s.rd ++ s.wr) (s.ea (kRegs j).1 (kRegs j).2) 16 := by
    rw [kRegs_ea G s h.consts j hj, h.consts.frame.rd]
    exact inRegions_of_mem hwf.hrdK (by norm_num) _ _ (by simp only; omega)
  obtain ⟨t, ht⟩ := group_exec j s hperm
  refine WP.block_intro _ ht ?_
  obtain ⟨hkw, hw⟩ := head_facts G hwf blk j hj s h
  -- the intermediate states
  set q := 4 * (j % 2) with hq
  have hq8 : q + 3 < 8 := by omega
  set s1 := headPost (j % 4) (kRegs j).1 (kRegs j).2 (Nat.blt j 12) s with hs1
  set s2 := stepPost q s1
  set s3 := stepPost (q + 1) s2
  set s4 := stepPost (q + 2) s3
  set s5 := stepPost (q + 3) s4
  have hpost : groupPost j s = s5 := rfl
  rw [hpost]
  -- registers the steps do not touch
  have keep : ∀ x, stepTouched x = false → s5.getV x = s1.getV x := fun x hx => by
    simp only [s5, s4, s3, s2]
    rw [stepPost_getV _ (by omega) _ _ hx, stepPost_getV _ (by omega) _ _ hx,
      stepPost_getV _ (by omega) _ _ hx, stepPost_getV _ (by omega) _ _ hx]
  have same15 : Same s1 s5 :=
    (((stepPost_same _ _).trans (stepPost_same _ _)).trans (stepPost_same _ _)).trans (stepPost_same _ _)
  have same05 : Same s s5 := (headPost_same _ _ _ _ _).trans same15
  have keep0 : ∀ x, stepTouched x = false → headTouched x = false → s5.getV x = s.getV x :=
    fun x h1 h2 => (keep x h1).trans (headPost_getV _ _ _ _ _ x h2)
  have hg : ∀ r, s5.getG r = s.getG r := fun r => congrArg (GRegs.get · r) same05.g
  -- the rounds
  have hv12 : ∀ r, r < 8 → ∀ s', Same s1 s' → s'.getV .v12 = s1.getV .v12 →
      s'.getV .v12 = s1.getV .v12 := fun _ _ _ _ h => h
  have k12 : ∀ r, r < 8 → ∀ s', (stepPost r s').getV .v12 = s'.getV .v12 :=
    fun r hr s' => stepPost_getV r hr s' .v12 rfl
  have hq4 : ∀ i, i < 4 → (q + i) % 4 = i := fun i hi => by omega
  have r1 := step_vars q (by omega) s1 _ K[4 * j]! (Wt (G.Mb blk) (4 * j))
    (by
      have := h.vars
      rw [VarsAt_mod] at this ⊢
      have e : 4 * j % 8 = q % 8 := by omega
      rw [e] at this
      have hx : ∀ x, headTouched x = false → s1.getV x = s.getV x :=
        headPost_getV _ _ _ _ _
      simp only [VarsAt] at this ⊢
      have e0 : ∀ k, k < 8 → headTouched (varReg (q % 8) k) = false := fun k hk => by
        unfold varReg; split <;> rfl
      rw [hx _ (e0 0 (by decide)), hx _ (e0 1 (by decide)), hx _ (e0 2 (by decide)),
        hx _ (e0 3 (by decide)), hx _ (e0 4 (by decide)), hx _ (e0 5 (by decide)),
        hx _ (e0 6 (by decide)), hx _ (e0 7 (by decide))]
      exact this)
    (by rw [show q % 4 = 0 by omega]; simpa using hkw 0 (by decide))
  have r2 := step_vars (q + 1) (by omega) s2 _ K[4 * j + 1]! (Wt (G.Mb blk) (4 * j + 1)) r1
    (by rw [hq4 1 (by decide), k12 _ (by omega)]; exact hkw 1 (by decide))
  have r3 := step_vars (q + 2) (by omega) s3 _ K[4 * j + 2]! (Wt (G.Mb blk) (4 * j + 2)) r2
    (by rw [hq4 2 (by decide), k12 _ (by omega), k12 _ (by omega)]; exact hkw 2 (by decide))
  have r4 := step_vars (q + 3) (by omega) s4 _ K[4 * j + 3]! (Wt (G.Mb blk) (4 * j + 3)) r3
    (by rw [hq4 3 (by decide), k12 _ (by omega), k12 _ (by omega), k12 _ (by omega)]
        exact hkw 3 (by decide))
  refine ⟨h.consts.same same05 (fun x hx => keep0 x ?_ ?_), ?_, fun i hi hji => ?_, ?_, ?_, ?_, ?_⟩
  · rcases hx with hx | rfl | rfl
    · exact stepTouched_nonvolatile x hx
    · rfl
    · rfl
  · rcases hx with hx | rfl | rfl
    · cases x <;> first | rfl | cases hx
    · rfl
    · rfl
  · rw [varsAt_four _ _ hM j hj, VarsAt_mod]
    rw [VarsAt_mod] at r4
    rw [show 4 * (j + 1) % 8 = (q + 3 + 1) % 8 by omega]
    exact r4
  · rw [keep _ (by unfold wreg; split <;> rfl)]
    exact hw i hi hji
  · rw [keep0 _ rfl rfl]; exact h.v16
  · rw [keep0 _ rfl rfl]; exact h.v17
  · rw [hg]; exact h.r4
  · rw [hg]; exact h.r5

theorem groups_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (s : State) (h : GroupInv G blk 0 s) :
    WP isa (.block groups) s (GroupInv G blk 16) := by
  have := WP.block_iter (M := isa) groupCode (GroupInv G blk) 0 16
    (fun i hi s hs => by simpa using group_ok G hwf blk i hi s (by simpa using hs)) s h
  simpa [groups] using this

end CC.Ppc.SHA256P8
