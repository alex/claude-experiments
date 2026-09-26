import ClaudeCrypto.Ppc.SHA256.P8Block

/-!
# The ppc64le SHA-256 block function: one block, and the loop
-/

namespace CC.Ppc.SHA256P8

open CC.Spec.SHA256

set_option linter.unusedSimpArgs false

/-- The invariant at the head of the per-block loop. -/
structure LoopInv (G : Ghost) (blk : Nat) (s : State) : Prop where
  consts : Consts G s
  v16 : s.getV .v16 = hv0 (G.Hb blk)
  v17 : s.getV .v17 = hv1 (G.Hb blk)
  r4 : s.getG .r4 = G.inp + BitVec.ofNat 64 (64 * blk)
  r5 : s.getG .r5 = -BitVec.ofNat 64 (G.n - blk)

theorem Consts.update {G : Ghost} {s s' : State} (h : Consts G s) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hl : s'.labels = s.labels) (hlr : s'.lr = s.lr)
    (hvsr : s'.vsr = s.vsr) (hcr : s'.cr1to7 = s.cr1to7)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r5 → s'.getG r = s.getG r)
    (hv : ∀ r, r.nonvolatile = true ∨ r = .v18 ∨ r = .v19 → s'.getV r = s.getV r) : Consts G s' := by
  have hF : Frame G.s0 s' :=
    ⟨hm.trans h.frame.mem, hrd.trans h.frame.rd, hwr.trans h.frame.wr, hl.trans h.frame.labels,
      hlr.trans h.frame.lr, hvsr.trans h.frame.vsr, hcr.trans h.frame.cr1to7,
      fun r hr => (hg r (by rintro rfl; cases hr) (by rintro rfl; cases hr) (by rintro rfl; cases hr)).trans
        (h.frame.g r hr),
      fun r hr => (hv r (Or.inl hr)).trans (h.frame.v r hr)⟩
  exact ⟨hF, (hg _ (by decide) (by decide) (by decide)).trans h.r6,
    (hg _ (by decide) (by decide) (by decide)).trans h.r10, (hg _ (by decide) (by decide) (by decide)).trans h.r11,
    (hg _ (by decide) (by decide) (by decide)).trans h.r12, (hg _ (by decide) (by decide) (by decide)).trans h.r7,
    (hg _ (by decide) (by decide) (by decide)).trans h.r8, (hg _ (by decide) (by decide) (by decide)).trans h.r9,
    (hv _ (Or.inr (Or.inl rfl))).trans h.v18, (hv _ (Or.inr (Or.inr rfl))).trans h.v19⟩

/-- Field equalities of states built by `setV`/`setG` chains. -/
macro "fld_tac" : tactic => `(tactic| simp only [loadMsgPost, finishPost, unpackPost, State.setG_mem,
  State.setV_mem, State.setG_rd, State.setV_rd, State.setG_wr, State.setV_wr, State.setG_labels,
  State.setV_labels, State.setG_lr, State.setV_lr, State.setG_vsr, State.setV_vsr, State.setG_cr1to7,
  State.setV_cr1to7])

/-! ## Loading the message block -/

/-- A message word, loaded little-endian and byte-reversed. -/
theorem msg_word (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (w : Nat) (hw : w < 16) :
    bswap (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 4 * w)) 32) = msgWord G.msg blk w := by
  rw [bswap_readW]
  have e : ∀ c : Nat, G.inp + BitVec.ofNat 64 (64 * blk + 4 * w) + BitVec.ofNat 64 c =
      G.inp + BitVec.ofNat 64 (64 * blk + 4 * w + c) := fun c => add_ofNat_add _ _ _
  have e1 : G.inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 1 = _ := e 1
  have e2 : G.inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 2 = _ := e 2
  have e3 : G.inp + BitVec.ofNat 64 (64 * blk + 4 * w) + 3 = _ := e 3
  rw [e1, e2, e3, msgWord, wordBE, hwf.hmsg _ (by omega), hwf.hmsg _ (by omega),
    hwf.hmsg _ (by omega), hwf.hmsg _ (by omega)]

/-- Four message words, as loaded by `lxvw4x` + `vperm`. -/
theorem msg_vec (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (k : Nat) (hk : k < 4) :
    vperm (lxv G.s0.mem (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k)))
      (lxv G.s0.mem (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k))) bswapVec = packW (Wt (G.Mb blk)) k := by
  have e : ∀ c : Nat, G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + BitVec.ofNat 64 (4 * c) =
      G.inp + BitVec.ofNat 64 (64 * blk + 4 * (4 * k + c)) := fun c => by
    rw [add_ofNat_add]; congr 2; ring
  have e1 : G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 4 = _ := e 1
  have e2 : G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 8 = _ := e 2
  have e3 : G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 12 = _ := e 3
  have e0 : G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) = G.inp + BitVec.ofNat 64 (64 * blk + 4 * (4 * k + 0)) := by
    congr 2; ring
  have hM : ∀ c, c < 4 → Wt (G.Mb blk) (4 * k + c) = msgWord G.msg blk (4 * k + c) := fun c _ => by
    rw [Wt_lt _ _ (by omega), Ghost.Mb, msgBlock_getElem _ _ _ (by omega)]
  rw [show lxv G.s0.mem (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k)) =
      w4 (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k)) 32)
        (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 4) 32)
        (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 8) 32)
        (G.s0.mem.readW (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) + 12) 32) from rfl,
    vperm_bswap, e1, e2, e3, e0, msg_word G hwf blk hblk _ (by omega), msg_word G hwf blk hblk _ (by omega),
    msg_word G hwf blk hblk _ (by omega), msg_word G hwf blk hblk _ (by omega), packW,
    ← hM 0 (by decide), ← hM 1 (by decide), ← hM 2 (by decide), ← hM 3 (by decide), Nat.add_zero]

theorem start_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) : WP isa (.block (unpack ++ loadMsg)) s (GroupInv G blk 0) := by
  apply WP.block_append
  obtain ⟨t1, ht1⟩ := unpack_exec s
  refine WP.block_intro _ ht1 ?_
  set s1 := unpackPost s with hs1
  have hg1 : ∀ r, s1.getG r = s.getG r := fun _ => rfl
  have hr4 : s1.getG .r4 = G.inp + BitVec.ofNat 64 (64 * blk) := (hg1 _).trans h.r4
  have hp : ∀ k, k < 4 → InRegions (s1.rd ++ s1.wr) (G.inp + BitVec.ofNat 64 (64 * blk + 16 * k)) 16 :=
    fun k hk => by
      rw [show s1.rd = G.s0.rd from h.consts.frame.rd]
      exact inRegions_of_mem hwf.hrdm (by simp only; have := hwf.hn; omega) _ _ (by simp only; omega)
  have a0 : s1.getG .r4 = G.inp + BitVec.ofNat 64 (64 * blk + 16 * 0) := by rw [hr4]; simp
  have ak : ∀ (r : GReg) (k : Nat), s1.getG r = BitVec.ofNat 64 (16 * k) →
      s1.getG .r4 + s1.getG r = G.inp + BitVec.ofNat 64 (64 * blk + 16 * k) := fun r k e => by
    rw [hr4, e, add_ofNat_add]
  have a1 := ak .r7 1 ((hg1 _).trans h.consts.r7)
  have a2 := ak .r8 2 ((hg1 _).trans h.consts.r8)
  have a3 := ak .r9 3 ((hg1 _).trans h.consts.r9)
  obtain ⟨t2, ht2⟩ := loadMsg_exec s1 (by rw [a0]; exact hp 0 (by decide)) (by rw [a1]; exact hp 1 (by decide))
    (by rw [a2]; exact hp 2 (by decide)) (by rw [a3]; exact hp 3 (by decide))
  refine WP.block_intro _ ht2 ?_
  have hmem : s1.mem = G.s0.mem := h.consts.frame.mem
  have h19 : s1.getV .v19 = bswapVec := h.consts.v19
  have hv : ∀ x : VReg, x.nonvolatile = true ∨ x = .v16 ∨ x = .v17 ∨ x = .v18 ∨ x = .v19 →
      (loadMsgPost s1).getV x = s.getV x := fun x hx => by
    rw [hs1]
    rcases hx with hx | rfl | rfl | rfl | rfl
    · cases x <;> first | (cases hx; done) |
        simp only [loadMsgPost, unpackPost, State.setG_getV, State.getV_setV, reduceCtorEq, ite_false]
    all_goals simp only [loadMsgPost, unpackPost, State.setG_getV, State.getV_setV, reduceCtorEq,
      ite_false]
  refine ⟨?_, ?_, fun i hi _ => ?_, ?_, ?_, ?_, ?_⟩
  · refine h.consts.update (by rw [hs1]; fld_tac) (by rw [hs1]; fld_tac) (by rw [hs1]; fld_tac)
      (by rw [hs1]; fld_tac) (by rw [hs1]; fld_tac) (by rw [hs1]; fld_tac)
      (by rw [hs1]; fld_tac) (fun r h0 h4 h5 => ?_) (fun r hr => hv r ?_)
    · simp only [loadMsgPost]; rw [State.getG_setG_ne _ _ _ _ h4]; simp only [State.setV_getG]; rfl
    · rcases hr with hr | rfl | rfl
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · -- the working variables: the unpacked hash value
    have hx : ∀ x : VReg, x = .v0 ∨ x = .v1 ∨ x = .v2 ∨ x = .v3 ∨ x = .v4 ∨ x = .v5 ∨ x = .v6 ∨
        x = .v7 → (loadMsgPost s1).getV x = s1.getV x := fun x hx => by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [loadMsgPost, State.setG_getV, State.getV_setV, reduceCtorEq, ite_false]
    have h16 := h.v16; have h17 := h.v17
    obtain ⟨b1, b2, b3⟩ := word_vsldoi_self (s.getV .v16)
    obtain ⟨f1, f2, f3⟩ := word_vsldoi_self (s.getV .v17)
    simp only [VarsAt, varReg, Nat.zero_mod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.mul_zero,
      varsAt_zero, initVars]
    rw [hx _ (by simp), hx _ (by simp), hx _ (by simp), hx _ (by simp), hx _ (by simp),
      hx _ (by simp), hx _ (by simp), hx _ (by simp)]
    simp only [s1, unpackPost, State.getV_setV, reduceCtorEq, ite_true, ite_false, word_vor_self, b1, b2,
      b3, f1, f2, f3, h16, h17, vsldoi_4, vsldoi_8, vsldoi_12, hv0, hv1, word_w4_0, word_w4_1, word_w4_2, word_w4_3]
    constructor <;> simp only [BitVec.or_self, word_w4_0, word_w4_1, word_w4_2, word_w4_3]
  · -- the message schedule
    have m0 := msg_vec G hwf blk hblk 0 (by decide)
    have m1 := msg_vec G hwf blk hblk 1 (by decide)
    have m2 := msg_vec G hwf blk hblk 2 (by decide)
    have m3 := msg_vec G hwf blk hblk 3 (by decide)
    rw [← hmem, ← h19, ← a0] at m0
    rw [← hmem, ← h19, ← a1] at m1
    rw [← hmem, ← h19, ← a2] at m2
    rw [← hmem, ← h19, ← a3] at m3
    simp only [Nat.zero_add]
    interval_cases i <;>
      simp only [loadMsgPost, wreg, Nat.reduceMod, State.setG_getV, State.getV_setV, reduceCtorEq,
        ite_true, ite_false, m0, m1, m2, m3]
  · rw [hv _ (Or.inr (Or.inl rfl))]; exact h.v16
  · rw [hv _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.v17
  · show s1.getG .r4 + 64#64 = _
    rw [hr4, show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, add_ofNat_add]
    congr 2
  · exact h.r5

/-! ## Adding the working variables into the hash value -/

theorem Hb_succ (G : Ghost) (blk : Nat) :
    hv0 (G.Hb (blk + 1)) =
      vadduwm (hv0 (G.Hb blk)) (w4 (varsAt (G.Hb blk) (G.Mb blk) 64).a (varsAt (G.Hb blk) (G.Mb blk) 64).b
        (varsAt (G.Hb blk) (G.Mb blk) 64).c (varsAt (G.Hb blk) (G.Mb blk) 64).d) ∧
    hv1 (G.Hb (blk + 1)) =
      vadduwm (hv1 (G.Hb blk)) (w4 (varsAt (G.Hb blk) (G.Mb blk) 64).e (varsAt (G.Hb blk) (G.Mb blk) 64).f
        (varsAt (G.Hb blk) (G.Mb blk) 64).g (varsAt (G.Hb blk) (G.Mb blk) 64).h) := by
  rw [Ghost.Hb, stateAfter_succ, compress_eq, ← Ghost.Hb, ← Ghost.Mb]
  generalize varsAt (G.Hb blk) (G.Mb blk) 64 = v
  constructor <;>
    simp only [hv0, hv1, vadduwm_w4, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_comm]

theorem neg_succ_add_one (m : Nat) :
    -BitVec.ofNat 64 (m + 1) + 1#64 = -BitVec.ofNat 64 m := by
  rw [← ofNat_add_ofNat]
  show -(BitVec.ofNat 64 m + BitVec.ofNat 64 1) + BitVec.ofNat 64 1 = _
  abel

theorem finish_ok (G : Ghost) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : GroupInv G blk 16 s) :
    WP isa (.block finish) s (fun s' => LoopInv G (blk + 1) s' ∧ s'.eq = some (s'.getG .r5 == 0#64)) := by
  obtain ⟨t, ht⟩ := finish_exec s
  refine WP.block_intro _ ht ?_
  obtain ⟨ha, he⟩ := Hb_succ G blk
  have hv := h.vars
  simp only [VarsAt, varReg, show 4 * 16 = 64 from rfl, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at hv
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · refine h.consts.update (by fld_tac) (by fld_tac) (by fld_tac) (by fld_tac) (by fld_tac) (by fld_tac)
      (by fld_tac) (fun r h0 h4 h5 => ?_) (fun r hr => ?_)
    · show (State.setG _ .r5 _).getG r = _
      rw [State.getG_setG_ne _ _ _ _ h5]; simp only [State.setV_getG]
    · simp only [finishPost, State.getV, State.setG, State.setV, VRegs.get_set]
      rcases hr with hr | rfl | rfl
      · cases r <;> first | (cases hr; done) | simp only [reduceCtorEq, ite_false]
      all_goals simp only [reduceCtorEq, ite_false]
  · show vadduwm (s.getV .v16) _ = _
    rw [pack_eq, hv.a, hv.b, hv.c, hv.d, h.v16, ha]
  · show vadduwm (s.getV .v17) _ = _
    rw [pack_eq, hv.e, hv.f, hv.g, hv.h, h.v17, he]
  · exact h.r4
  · show s.getG .r5 + 1#64 = _
    rw [h.r5, show G.n - blk = G.n - (blk + 1) + 1 by omega, neg_succ_add_one]

theorem block_ok (G : Ghost) (hwf : G.WF) (blk : Nat) (hblk : blk < G.n) (s : State)
    (h : LoopInv G blk s) :
    WP isa (.block blockCode) s (fun s' => LoopInv G (blk + 1) s' ∧ s'.eq = some (s'.getG .r5 == 0#64)) := by
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (start_ok G hwf blk hblk s h) ?_
  intro s1 h1
  refine WP.mono (groups_ok G hwf blk s1 h1) ?_
  intro s2 h2
  exact finish_ok G blk hblk s2 h2

/-! ## The loop -/

theorem neg_ofNat_eq_zero (k : Nat) (hk : k < 2 ^ 64) : (-BitVec.ofNat 64 k == 0#64) = (k == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, show (0#64 : BitVec 64) = 0 from rfl, neg_eq_zero]
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
    exact this
  · rintro rfl; rfl

theorem loop_ok (G : Ghost) (hwf : G.WF) (s : State) (hn0 : 0 < G.n) (h : LoopInv G 0 s) :
    WP isa (.loop (.block blockCode) .ne) s (LoopInv G G.n) := by
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => 0 < m ∧ m ≤ G.n ∧ LoopInv G (G.n - m) s) ?_
    G.n s ⟨hn0, le_refl _, by simpa using h⟩
  rintro m s ⟨hm0, hmn, hinv⟩
  refine WP.mono (block_ok G hwf (G.n - m) (by omega) s hinv) ?_
  rintro s' ⟨hinv', heq⟩
  have hx5 := hinv'.r5
  have e : G.n - (G.n - m + 1) = m - 1 := by omega
  rw [e] at hx5
  have hm : m - 1 < 2 ^ 64 := by have := hwf.hn; omega
  have hc : isa.eval .ne s' = some (!(m - 1 == 0)) := by
    simp only [isa, evalCond, heq, hx5, neg_ofNat_eq_zero _ hm, Option.map_some]
  by_cases hm1 : m = 1
  · subst hm1
    left
    refine ⟨by rw [hc]; rfl, ?_⟩
    have : G.n - 1 + 1 = G.n := by omega
    rwa [this] at hinv'
  · right
    refine ⟨?_, m - 1, by omega, by omega, by omega, ?_⟩
    · rw [hc]; congr 1; simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]; omega
    · have : G.n - m + 1 = G.n - (m - 1) := by omega
      rwa [this] at hinv'

end CC.Ppc.SHA256P8
