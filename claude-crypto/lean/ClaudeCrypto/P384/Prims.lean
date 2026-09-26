import ClaudeCrypto.P384.PrimLemmas

/-!
# Specifications of the straight-line primitives of `P384/Prog.lean`
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- Registers other than `vs` are unchanged. -/
def RegsExcept (vs : List Var) (s q : State) : Prop := ∀ v, v ∉ vs → q.r v = s.r v

theorem RegsExcept.trans {vs ws : List Var} {s q u : State} (h1 : RegsExcept vs s q) (h2 : RegsExcept ws q u) :
    RegsExcept (vs ++ ws) s u := fun v hv => by
  simp only [List.mem_append, not_or] at hv
  rw [h2 v hv.2, h1 v hv.1]

theorem RegsExcept.mono {vs ws : List Var} {s q : State} (h : RegsExcept vs s q) (hw : ∀ v ∈ vs, v ∈ ws) :
    RegsExcept ws s q := fun v hv => h v (fun h' => hv (hw v h'))

/-- A block that does not write memory. -/
theorem eff_of_mem {s q : State} (h13 : q.r 13 = s.r 13) (h14 : q.r 14 = s.r 14) (hm : q.mem = s.mem)
    (hrd : q.rd = s.rd) (hwr : q.wr = s.wr) (hl : q.labels = s.labels) : Eff [] s q := by
  refine ⟨⟨h13, h14, hrd, hwr, hl, fun a _ => by rw [hm]⟩, fun i _ _ => ?_, ?_⟩
  · unfold sv slotVal slotAddr; rw [hm, h14]
  · unfold cnt; rw [hm, h14]

theorem regsExcept9 {s q : State} (h : ∀ v, v ≠ 9 → q.r v = s.r v) : RegsExcept [9] s q :=
  fun v hv => h v (by simpa using hv)

theorem copySlot_exec (d a : Nat) (s : State) (h : Inv s) (hd : d < nSlots) (ha : a < nSlots) :
    ∃ q, execBlock isa (copySlot d a) s = some q ∧ Eff [d] s q.1 ∧ sv q.1 d = sv s a ∧
      RegsExcept [9] s q.1 ∧ q.1.cf = s.cf ∧ q.1.sub = s.sub := by
  have hprog : copySlot d a = (List.range 6).flatMap (stBody (fun k => [.ld 9 14 (slotOff a + 8 * k)]) d) := rfl
  obtain ⟨q, hq, hst⟩ := st_iter s h d hd (fun k => [.ld 9 14 (slotOff a + 8 * k)])
    (fun k => s.mem.readW (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * k)) 64)
    (fun k hk s' hs' => by
      have hp : InRegions (s'.rd ++ s'.wr) (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * k)) 8 := by
        rw [hs'.rd, hs'.wr]
        exact (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s h a ha k hk))
      refine exec1_some ?_
      simp only [isa, Limb.exec, Limb.State.load, hs'.r14, hp, ite_true, Option.map_some]
      rw [hs'.readW _ (by
        rw [slotAddr_eq]
        refine sep_frame _ _ _ _ ?_ ?_ ?_ <;> simp only [slotOff_eq] <;> have := nSlots_eq <;> omega)])
  obtain ⟨he, hv, hr, hcf, hsub⟩ := st_done s d hd _ q.1 hst
  refine ⟨q, hprog ▸ hq, he, ?_, regsExcept9 hr, hcf, hsub⟩
  rw [hv]; unfold sv slotVal mval; apply lsum_congr; intro k _
  unfold mlimb; rw [slotAddr_eq, addr_add_ofNat']

theorem copyConst_exec (d c : Nat) (s : State) (h : Inv s) (hd : d < nSlots) (hc : c + 48 ≤ constSize) :
    ∃ q, execBlock isa (copyConst d c) s = some q ∧ Eff [d] s q.1 ∧ sv q.1 d = cval s c ∧
      RegsExcept [9] s q.1 ∧ q.1.cf = s.cf ∧ q.1.sub = s.sub := by
  have hprog : copyConst d c = (List.range 6).flatMap (stBody (fun k => [.ld 9 13 (c + 8 * k)]) d) := rfl
  obtain ⟨q, hq, hst⟩ := st_iter s h d hd (fun k => [.ld 9 13 (c + 8 * k)])
    (fun k => s.mem.readW (s.r 13 + BitVec.ofNat 64 (c + 8 * k)) 64)
    (fun k hk s' hs' => by
      have h13 : s'.r 13 = s.r 13 := hs'.regs 13 (by decide)
      have hp : InRegions (s'.rd ++ s'.wr) (s.r 13 + BitVec.ofNat 64 (c + 8 * k)) 8 := by
        rw [hs'.rd, hs'.wr]; exact const_in s h _ (by omega)
      refine exec1_some ?_
      simp only [isa, Limb.exec, Limb.State.load, h13, hp, ite_true, Option.map_some]
      rw [hs'.readW _ (fun hk0 => by
        rw [slotAddr_eq, slotOff_eq]
        exact h.sep.mono _ _ _ _ (by have := nSlots_eq; have := frameSize_eq; omega) (by omega) hk0
          (by decide))])
  obtain ⟨he, hv, hr, hcf, hsub⟩ := st_done s d hd _ q.1 hst
  refine ⟨q, hprog ▸ hq, he, ?_, regsExcept9 hr, hcf, hsub⟩
  rw [hv]; unfold cval mval; apply lsum_congr; intro k _
  unfold mlimb; rw [addr_add_ofNat']

set_option exponentiation.threshold 400 in
theorem zeroSlot_exec (d : Nat) (s : State) (h : Inv s) (hd : d < nSlots) :
    ∃ q, execBlock isa (zeroSlot d) s = some q ∧ Eff [d] s q.1 ∧ sv q.1 d = 0 ∧
      RegsExcept [9] s q.1 ∧ q.1.cf = s.cf ∧ q.1.sub = s.sub := by
  set s1 := s.set 9 0 with hs1
  have e13 : s1.r 13 = s.r 13 := by simp [hs1]
  have e14 : s1.r 14 = s.r 14 := by simp [hs1]
  have eff1 : Eff [] s s1 := eff_of_mem e13 e14 rfl rfl rfl rfl
  have h1 : Inv s1 := h.frm eff1.frm
  have hprog : (List.range 6).map (fun k => Instr.st 14 (slotOff d + 8 * k) 9) =
      (List.range 6).flatMap (stBody (fun _ => []) d) := by
    simp [stBody, List.range_succ]
  obtain ⟨q, hq, hst⟩ := st_iter s1 h1 d hd (fun _ => []) (fun _ => 0) (fun k hk s' hs' => by
    have : s'.set 9 0 = s' := by
      have e9 : s'.r 9 = 0 := by rw [hs'.r9]; split_ifs <;> simp [hs1]
      cases s'; simp only [Limb.State.set, Limb.State.mk.injEq, and_true]
      rw [← e9]; exact Function.update_eq_self _ _
    exact ⟨[], by rw [this]; rfl⟩)
  obtain ⟨he, hv, hr, hcf, hsub⟩ := st_done s1 d hd _ q.1 hst
  refine ⟨(q.1, q.2), ?_, (eff1.trans he).mono (by simp), by rw [hv]; rfl, ?_, hcf, hsub⟩
  · simp only [zeroSlot, hprog, execBlock, isa, Limb.exec]
    erw [hq]; rfl
  · refine regsExcept9 (fun v hv => ?_)
    rw [hr v hv, hs1]; simp [Limb.State.set, Function.update_of_ne hv]

theorem loadBE_exec (d : Nat) (b : Var) (off : Nat) (s : State) (h : Inv s) (hd : d < nSlots)
    (hb9 : b ≠ 9) (hb14 : b ≠ 14) (hoff : off + 48 < 2 ^ 63)
    (hin : Within (s.rd ++ s.wr) (s.r b + BitVec.ofNat 64 off) 48)
    (hsep : Mem.Sep (s.r 14) frameSize (s.r b + BitVec.ofNat 64 off) 48) :
    ∃ q, execBlock isa (loadBE d b off) s = some q ∧ Eff [d] s q.1 ∧
      sv q.1 d = bytesToNat (inBytes s.mem (s.r b + BitVec.ofNat 64 off) 48) ∧
      RegsExcept [9] s q.1 ∧ q.1.cf = s.cf ∧ q.1.sub = s.sub := by
  have ea : ∀ k < 6, s.r b + BitVec.ofNat 64 (off + 40 - 8 * k) =
      s.r b + BitVec.ofNat 64 off + BitVec.ofNat 64 (40 - 8 * k) := fun k hk => by
    rw [addr_add_ofNat', show off + (40 - 8 * k) = off + 40 - 8 * k by omega]
  have hprog : loadBE d b off = (List.range 6).flatMap (stBody (fun k => [.ldbe 9 b (off + 40 - 8 * k)]) d) := rfl
  obtain ⟨q, hq, hst⟩ := st_iter s h d hd (fun k => [.ldbe 9 b (off + 40 - 8 * k)])
    (fun k => bswap64 (s.mem.readW (s.r b + BitVec.ofNat 64 (off + 40 - 8 * k)) 64))
    (fun k hk s' hs' => by
      have hrb : s'.r b = s.r b := hs'.regs b hb9
      have hp : InRegions (s'.rd ++ s'.wr) (s.r b + BitVec.ofNat 64 (off + 40 - 8 * k)) 8 := by
        rw [hs'.rd, hs'.wr, ea k hk]; exact hin.sub _ _ (by omega)
      refine exec1_some ?_
      simp only [isa, Limb.exec, Limb.State.load, hrb, hp, ite_true, Option.map_some]
      rw [hs'.readW _ (fun hk0 => by
        rw [slotAddr_eq, slotOff_eq, ea k hk]
        exact hsep.mono _ _ _ _ (by have := nSlots_eq; have := frameSize_eq; omega) (by omega) hk0
          (by decide))])
  obtain ⟨he, hv, hr, hcf, hsub⟩ := st_done s d hd _ q.1 hst
  refine ⟨q, hprog ▸ hq, he, ?_, regsExcept9 hr, hcf, hsub⟩
  rw [hv, bytesToNat_48]; apply lsum_congr; intro k hk
  rw [bswap64_readW, ea k hk]

theorem ltConst_exec (a c : Nat) (t : Var) (s : State) (h : Inv s) (ha : a < nSlots) (hc : c + 48 ≤ constSize)
    (ht8 : t ≠ 8) (ht9 : t ≠ 9) :
    ∃ q, execBlock isa (ltConst a c t) s = some q ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels ∧ q.1.r t = (if sv s a < cval s c then BitVec.allOnes 64 else 0) ∧
      RegsExcept [8, 9, t] s q.1 ∧ q.1.cf = none := by
  have hprog : ltConst a c t =
      [.ld 9 14 (slotOff a + 8 * 0), .ld 8 13 (c + 8 * 0), if true then .sub 9 8 else .sbb 9 8] ++
      ((List.range 5).map (fun i => ltBody a c (1 + i))).flatten ++ [.mask t, .clrc] := by
    simp [ltConst, ltBody, List.flatMap_def, Nat.add_comm]
  obtain ⟨q1, hq1, h1⟩ := lt_step s h a c ha hc 0 (by decide) s true (fun _ => rfl) (fun h => by cases h)
    (fun _ _ _ => rfl) rfl rfl rfl rfl
  obtain ⟨q2, hq2, h2⟩ := exec_iter (ltBody a c) (LtInv s a c) 1 5 (fun i hi s' hs' =>
    lt_step s h a c ha hc (1 + i) (by omega) s' false (fun h => by cases h) (fun _ => ⟨hs'.cf, hs'.sub⟩)
      hs'.regs hs'.mem hs'.rd hs'.wr hs'.labels) q1.1 h1
  have hcf := h2.cf
  have hsub := h2.sub
  obtain ⟨tr3, hq3⟩ : ∃ tr, execBlock isa [.mask t, .clrc] q2.1 = some
      ({ q2.1.set t (if decide (lsum (cmpA s a) 6 < lsum (cmpC s c) 6) then BitVec.allOnes 64 else 0)
        with cf := none }, tr) := by
    limb_sym [hcf, hsub]
    exact ⟨_, rfl⟩
  refine ⟨_, by rw [hprog]; exact exec_append (exec_append hq1 hq2) hq3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h2.mem
  · exact h2.rd
  · exact h2.wr
  · exact h2.labels
  · simp only [Limb.State.set, Function.update_self, decide_eq_true_eq]; rfl
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    simp only [Limb.State.set, Function.update_of_ne hv.2.2]
    exact h2.regs v hv.1 hv.2.1
  · rfl

/-- (The hypothesis `hd13` was added: for `d = 13` the base register of the constants table is
overwritten, so `Eff` does not hold.) -/
theorem topBit_exec (a : Nat) (d : Var) (s : State) (h : Inv s) (ha : a < nSlots) (hd7 : d ≠ 7) (hd8 : d ≠ 8)
    (hd14 : d ≠ 14) (hd13 : d ≠ 13) :
    ∃ q, execBlock isa (topBit a d) s = some q ∧ Eff [a] s q.1 ∧ sv q.1 a = 2 * sv s a % 2 ^ 384 ∧
      q.1.r d = BitVec.ofNat 64 (sv s a / 2 ^ 383) ∧ RegsExcept [d, 7, 8] s q.1 ∧ q.1.cf = none := by
  have hprog : topBit a d = [.ld d 14 (slotOff a + 40), .shr d 63] ++
      ((List.range 5).map (fun i => tbGroup a (5 - (0 + i)))).flatten ++
      [.ld 7 14 (slotOff a), .shl 7 1, .st 14 (slotOff a) 7] := by
    simp [topBit, tbGroup, List.flatMap_def]
  obtain ⟨q1, hq1, h1⟩ := tb_init s h a ha d hd14
  obtain ⟨q2, hq2, h2⟩ := exec_iter (fun j => tbGroup a (5 - j)) (TB s a d) 0 5 (fun i hi s' hs' =>
    tb_step s h a ha d hd7 hd8 hd14 (0 + i) (by omega) s' hs') q1.1 h1
  obtain ⟨q3, hq3, h3⟩ := tb_last s h a ha d hd7 hd8 hd14 q2.1 h2
  have hag : Mem.Agree s.mem q3.1.mem ⟨slotAddr 0 s a, 48⟩ := by
    have := h3.agree; simpa using this
  have h14 : q3.1.r 14 = s.r 14 := h3.regs 14 (Ne.symm hd14) (by decide) (by decide)
  have hsv : sv q3.1 a = lsum (fun k => (tbN s a k).toNat) 6 := by
    unfold sv slotVal mval
    rw [show slotAddr 0 q3.1 a = slotAddr 0 s a by rw [slotAddr, slotAddr, h14]]
    exact lsum_congr _ _ _ (fun k hk => h3.lim k hk (by omega))
  have hsv0 : sv s a = lsum (fun k => (tbA s a k).toNat) 6 := rfl
  obtain ⟨m1, m2⟩ := topBit_math (fun k => (tbA s a k).toNat) (fun k => BitVec.isLt _)
  refine ⟨(q3.1, q1.2 ++ q2.2 ++ q3.2), by rw [hprog]; exact exec_append (exec_append hq1 hq2) hq3,
    eff_of_slot_agree a ha (h3.regs 13 (Ne.symm hd13) (by decide) (by decide)) h14 h3.rd h3.wr h3.labels hag,
    ?_, ?_, fun v hv => ?_, h3.cf⟩
  · rw [hsv, hsv0, ← m1]
    exact lsum_congr _ _ _ (fun k _ => tbN_toNat s a k)
  · rw [h3.rdv, hsv0, m2]
    apply BitVec.eq_of_toNat_eq
    rw [shr63_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := (tbA s a 5).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    exact h3.regs v hv.1 hv.2.1 hv.2.2

/-- Writing the counter cell keeps the frame and the slots. -/
theorem cnt_write (s : State) (x : BitVec 64) (m : Mem) (hm : m = s.mem.writeW (s.r 14 + BitVec.ofNat 64 cntOff) x) :
    Mem.Agree s.mem m ⟨s.r 14, frameSize⟩ ∧ ∀ i < nSlots, mval m (slotAddr 0 s i) 6 = sv s i := by
  subst hm
  refine ⟨(Mem.Agree.refl _ _).writeW _ _ (Region.contains_offset _ _ _ _ (by decide) (by decide)), fun i hi => ?_⟩
  unfold sv slotVal mval; apply lsum_congr; intro k hk; unfold mlimb
  rw [slotAddr_eq, addr_add_ofNat', Mem.readW_writeW_sep]
  exact sep_offsets _ _ _ _ _ (by rw [slotOff_eq]; have := nSlots_eq; rw [cntOff_eq]; omega)
    (by decide) (by rw [slotOff_eq]; have := nSlots_eq; omega) (by decide) (by decide)

theorem cntInit_exec (k : Nat) (s : State) (h : Inv s) :
    ∃ q, execBlock isa (cntInit k) s = some q ∧ Frm s q.1 ∧ (∀ i < nSlots, sv q.1 i = sv s i) ∧
      cnt q.1 = BitVec.ofNat 64 k ∧ RegsExcept [9] s q.1 ∧ q.1.cf = s.cf ∧ q.1.sub = s.sub := by
  have hp := frame_sub s h cntOff 8 (by decide)
  have n14 : (14 : Var) ≠ 9 := by decide
  simp only [cntInit]
  limb_sym [hp, n14]
  obtain ⟨hag, hsv⟩ := cnt_write s _ _ rfl
  refine ⟨_, rfl, ⟨by simp, by simp, rfl, rfl, rfl, hag⟩, fun i hi => ?_, ?_, ?_, rfl, rfl⟩
  · rw [← hsv i hi]; unfold sv slotVal slotAddr; simp
  · unfold cnt; simp
  · refine regsExcept9 (fun v hv => ?_); simp [Function.update_of_ne hv]

theorem cntDec_exec (s : State) (h : Inv s) :
    ∃ q, execBlock isa cntDec s = some q ∧ Frm s q.1 ∧ (∀ i < nSlots, sv q.1 i = sv s i) ∧
      cnt q.1 = cnt s - 1 ∧ q.1.r 9 = cnt s - 1 ∧ RegsExcept [9] s q.1 ∧ q.1.cf = none := by
  have hp := frame_sub s h cntOff 8 (by decide)
  have hp' : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 cntOff) 8 :=
    (inRegions_append _ _ _ _).mpr (Or.inr hp)
  have n14 : (14 : Var) ≠ 9 := by decide
  simp only [cntDec]
  limb_sym [hp, hp', n14]
  obtain ⟨hag, hsv⟩ := cnt_write s _ _ rfl
  refine ⟨_, rfl, ⟨by simp, by simp, rfl, rfl, rfl, hag⟩, fun i hi => ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hsv i hi]; unfold sv slotVal slotAddr; simp
  · unfold cnt; simp
  · simp; rfl
  · refine regsExcept9 (fun v hv => ?_); simp [Function.update_of_ne hv]

theorem orSlot_sv (a : Nat) (s : State) (h : Inv s) (ha : a < nSlots) :
    ∃ q, execBlock isa (orSlot 10 (slotOff a)) s = some q ∧ (q.1.r 10 = 0 ↔ sv s a = 0) ∧
      RegsExcept [10, 9] s q.1 ∧ q.1.cf = none ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  obtain ⟨q, hq, hz, hr, hcf, hm, hrd, hwr, hl⟩ := orSlot_exec 10 (slotOff a) s (by decide) (by decide)
    (fun k hk => (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s h a ha k hk)))
  refine ⟨q, hq, hz, fun v hv => ?_, hcf, hm, hrd, hwr, hl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  exact hr v hv.1 hv.2

end CC.P384
