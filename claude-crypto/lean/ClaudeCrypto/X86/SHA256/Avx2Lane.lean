import ClaudeCrypto.X86.SHA256.Avx2Round
import ClaudeCrypto.X86.SHA256.Avx2Buf

/-! # AVX2 SHA-256: the schedule window and the interleaved schedule steps of lane 0 -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

theorem Wt_recur (M : List Word) : Recur (Wt M) := by
  intro n hn
  rw [Wt_ge M n hn]
  abel

theorem ymm_ne (a b : Nat) (ha : a < 4) (hb : b < 4) (h : a ≠ b) : ymm a ≠ ymm b := by
  interval_cases a <;> interval_cases b <;> first | decide | exact absurd rfl h

theorem ymm_ne4 (a : Nat) (ha : a < 4) : ymm a ≠ .y4 ∧ ymm a ≠ .y5 ∧ ymm a ≠ .y6 ∧ ymm a ≠ .y7 := by
  interval_cases a <;> decide

/-- `SliceFrame` preserves the window register `ymm b` for `b ≠ g % 4`. -/
theorem SliceFrame.ymm {g : Nat} {s s' : State} (h : SliceFrame g s s') (b : Nat) (hb : b < 4)
    (hne : b ≠ g % 4) : s'.getV (ymm b) = s.getV (ymm b) :=
  h.2.2.2.2.2.2.2.2 _ (ymm_ne _ _ hb (Nat.mod_lt _ (by decide)) hne) (ymm_ne4 b hb).1 (ymm_ne4 b hb).2.1
    (ymm_ne4 b hb).2.2.1 (ymm_ne4 b hb).2.2.2

theorem SliceFrame.high {g : Nat} {s s' : State} (h : SliceFrame g s s') (v : VReg)
    (hv : v = .y10 ∨ v = .y11 ∨ v = .y12) : s'.getV v = s.getV v := by
  have hg : g % 4 < 4 := Nat.mod_lt _ (by decide)
  apply h.2.2.2.2.2.2.2.2 <;> rcases hv with rfl | rfl | rfl <;>
    first | decide | (generalize g % 4 = j at hg; interval_cases j <;> decide)

/-- The state of the schedule window before lane-0 round `t < 48`
(`g = t/4 + 4` is the group being computed, `t % 4` the quarters done). -/
def WinInv (WA WB : Nat → Word) (t : Nat) (s : State) : Prop :=
  HoldsGroup (s.getV (ymm ((t / 4 + 5) % 4))) WA WB (t / 4 + 1) ∧
  HoldsGroup (s.getV (ymm ((t / 4 + 6) % 4))) WA WB (t / 4 + 2) ∧
  HoldsGroup (s.getV (ymm ((t / 4 + 7) % 4))) WA WB (t / 4 + 3) ∧
  (t % 4 = 0 → HoldsGroup (s.getV (ymm ((t / 4 + 4) % 4))) WA WB (t / 4)) ∧
  (t % 4 = 1 → ∀ i < 8, lane 32 (s.getV (ymm ((t / 4 + 4) % 4))) i = part0 WA WB (t / 4 + 4) i) ∧
  (t % 4 = 2 → ∀ i < 8, lane 32 (s.getV (ymm ((t / 4 + 4) % 4))) i = part1 WA WB (t / 4 + 4) i) ∧
  (t % 4 = 3 → HoldsGroup (s.getV (ymm ((t / 4 + 4) % 4))) WA WB (t / 4 + 4))

/-- Facts about the `K` table needed by the schedule. -/
structure KFacts (s0 : State) (sp : Addr) : Prop where
  val : ∀ g < 16, ∀ i < 8, lane 32 (s0.mem.readW (kAddr s0 g) 256) i = K[4 * g + i % 4]!
  rd : ∀ g < 16, InRegions s0.rd (kAddr s0 g) 32
  sep : ∀ g < 16, Mem.Sep sp 512 (kAddr s0 g) 32

theorem SliceCtx.of_win {WA WB : Nat → Word} {t : Nat} {s : State} (h : WinInv WA WB t s)
    (m10 : s.getV .y10 = maskV shuf00BA) (m11 : s.getV .y11 = maskV shufDC00) :
    SliceCtx (t / 4 + 4) WA WB s := by
  obtain ⟨x1, x2, x3, -⟩ := h
  refine ⟨?_, ?_, ?_, m10, m11⟩
  · rw [show t / 4 + 4 - 3 = t / 4 + 1 by omega, show (t / 4 + 4 + 1) % 4 = (t / 4 + 5) % 4 by omega]; exact x1
  · rw [show t / 4 + 4 - 2 = t / 4 + 2 by omega, show (t / 4 + 4 + 2) % 4 = (t / 4 + 6) % 4 by omega]; exact x2
  · rw [show t / 4 + 4 - 1 = t / 4 + 3 by omega, show (t / 4 + 4 + 3) % 4 = (t / 4 + 7) % 4 by omega]; exact x3

/-- Moving from quarter `q < 3` to `q + 1` within a group. -/
theorem WinInv.next_quarter {WA WB : Nat → Word} {t : Nat} {s s' : State} (h : WinInv WA WB t s)
    (hq : t % 4 < 3) (hf : SliceFrame (t / 4 + 4) s s')
    (h1 : t % 4 = 0 → ∀ i < 8, lane 32 (s'.getV (ymm ((t / 4 + 4) % 4))) i = part0 WA WB (t / 4 + 4) i)
    (h2 : t % 4 = 1 → ∀ i < 8, lane 32 (s'.getV (ymm ((t / 4 + 4) % 4))) i = part1 WA WB (t / 4 + 4) i)
    (h3 : t % 4 = 2 → HoldsGroup (s'.getV (ymm ((t / 4 + 4) % 4))) WA WB (t / 4 + 4)) :
    WinInv WA WB (t + 1) s' := by
  obtain ⟨x1, x2, x3, -⟩ := h
  have e : (t + 1) / 4 = t / 4 := by omega
  unfold WinInv
  rw [e, hf.ymm ((t / 4 + 5) % 4) (Nat.mod_lt _ (by decide)) (by omega),
    hf.ymm ((t / 4 + 6) % 4) (Nat.mod_lt _ (by decide)) (by omega),
    hf.ymm ((t / 4 + 7) % 4) (Nat.mod_lt _ (by decide)) (by omega)]
  refine ⟨x1, x2, x3, fun h => absurd h (by omega), fun h => h1 (by omega), fun h => h2 (by omega),
    fun h => h3 (by omega)⟩

/-- Moving from quarter 3 of group `g` to quarter 0 of group `g + 1`. -/
theorem WinInv.next_group {WA WB : Nat → Word} {t : Nat} {s s' : State} (h : WinInv WA WB t s)
    (hq : t % 4 = 3) (hf : SliceFrame (t / 4 + 4) s s')
    (h0 : s'.getV (ymm ((t / 4 + 4) % 4)) = s.getV (ymm ((t / 4 + 4) % 4))) :
    WinInv WA WB (t + 1) s' := by
  obtain ⟨x1, x2, x3, -, -, -, x0⟩ := h
  have e : (t + 1) / 4 = t / 4 + 1 := by omega
  unfold WinInv
  rw [e, show (t / 4 + 1 + 5) % 4 = (t / 4 + 6) % 4 by omega, show (t / 4 + 1 + 6) % 4 = (t / 4 + 7) % 4 by omega,
    show (t / 4 + 1 + 7) % 4 = (t / 4 + 4) % 4 by omega, show (t / 4 + 1 + 4) % 4 = (t / 4 + 5) % 4 by omega,
    hf.ymm ((t / 4 + 5) % 4) (Nat.mod_lt _ (by decide)) (by omega),
    hf.ymm ((t / 4 + 6) % 4) (Nat.mod_lt _ (by decide)) (by omega),
    hf.ymm ((t / 4 + 7) % 4) (Nat.mod_lt _ (by decide)) (by omega), h0,
    show t / 4 + 1 + 1 = t / 4 + 2 by omega, show t / 4 + 1 + 2 = t / 4 + 3 by omega,
    show t / 4 + 1 + 3 = t / 4 + 4 by omega]
  refine ⟨x2, x3, x0 hq, fun _ => x1, fun h => absurd h (by omega), fun h => absurd h (by omega),
    fun h => absurd h (by omega)⟩

theorem region_contains_buf (sp : Addr) (g : Nat) (hg : g < 16) :
    (Region.mk sp 512).Contains (sp + BitVec.ofNat 64 (32 * g)) 32 :=
  Region.contains_offset _ _ _ _ (by omega) (by decide)

/-- One interleaved schedule step (after lane-0 round `t < 48`). -/
theorem sched_step (WA WB : Nat → Word) (hRA : Recur WA) (hRB : Recur WB) (sp : Addr) (rest : List Region)
    (s0 : State) (hk : KFacts s0 sp) (t : Nat) (ht : t < 48) (s : State)
    (hwin : WinInv WA WB t s) (hbuf : BufInv WA WB s.mem sp (t / 4 + 4))
    (m10 : s.getV .y10 = maskV shuf00BA) (m11 : s.getV .y11 = maskV shufDC00)
    (hrsp : s.gpr.rsp = sp) (hwr : s.wr = ⟨sp, 560⟩ :: rest) (hrd : s.rd = s0.rd)
    (hlab : s.labels = s0.labels) (hmem : Mem.Agree s0.mem s.mem ⟨sp, 512⟩) :
    ∃ q, execBlock isa (schedSlice (t / 4 + 4) (t % 4)) s = some q ∧ SliceFrame (t / 4 + 4) s q.1 ∧
      Mem.Agree s0.mem q.1.mem ⟨sp, 512⟩ ∧ BufInv WA WB q.1.mem sp ((t + 1) / 4 + 4) ∧
      (t + 1 < 48 → WinInv WA WB (t + 1) q.1) := by
  have hctx := SliceCtx.of_win hwin m10 m11
  have hg1 : 4 ≤ t / 4 + 4 := by omega
  have hg : t / 4 + 4 < 16 := by omega
  have hq : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hq with hq | hq | hq | hq
  · obtain ⟨q, hq1, hf, hm, hl⟩ := slice0_exec _ hg1 hg WA WB s hctx
      (by rw [show t / 4 + 4 - 4 = t / 4 by omega]; exact hwin.2.2.2.1 hq)
    rw [hq]
    refine ⟨q, hq1, hf, hm ▸ hmem, ?_, fun _ => ?_⟩
    · rw [hm, show (t + 1) / 4 = t / 4 by omega]; exact hbuf
    · exact hwin.next_quarter (by omega) hf (fun _ => hl) (fun h => absurd h (by omega))
        (fun h => absurd h (by omega))
  · obtain ⟨q, hq1, hf, hm, hl⟩ := slice1_exec _ hg1 hg WA WB hRA hRB s hctx (hwin.2.2.2.2.1 hq)
    rw [hq]
    refine ⟨q, hq1, hf, hm ▸ hmem, ?_, fun _ => ?_⟩
    · rw [hm, show (t + 1) / 4 = t / 4 by omega]; exact hbuf
    · exact hwin.next_quarter (by omega) hf (fun h => absurd h (by omega)) (fun _ => hl)
        (fun h => absurd h (by omega))
  · obtain ⟨q, hq1, hf, hm, hl⟩ := slice2_exec _ hg1 hg WA WB hRA hRB s hctx.m11 (hwin.2.2.2.2.2.1 hq)
    rw [hq]
    refine ⟨q, hq1, hf, hm ▸ hmem, ?_, fun _ => ?_⟩
    · rw [hm, show (t + 1) / 4 = t / 4 by omega]; exact hbuf
    · exact hwin.next_quarter (by omega) hf (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
        (fun _ => hl)
  · have hkr : InRegions s.rd (kAddr s (t / 4 + 4)) 32 := by
      rw [hrd, kAddr, hlab]; exact hk.rd _ hg
    obtain ⟨q, hq1, hf, h0, hm⟩ := slice3_exec _ hg sp rest s hkr hrsp hwr
    rw [hq]
    refine ⟨q, hq1, hf, ?_, ?_, fun _ => hwin.next_group hq hf h0⟩
    · rw [hm]; refine hmem.writeW _ _ ?_; exact region_contains_buf sp _ hg
    · rw [hm, show (t + 1) / 4 + 4 = t / 4 + 4 + 1 by omega]
      refine hbuf.step (by omega) _ _ (hwin.2.2.2.2.2.2 hq) ?_
      intro i hi
      have e : kAddr s (t / 4 + 4) = kAddr s0 (t / 4 + 4) := by rw [kAddr, kAddr, hlab]
      rw [e, hmem.readW _ _ (hk.sep _ hg), hk.val _ hg i hi]

/-! ## The rounds -/

/-- `Σ₀` of the previous round's `a`, which round `t` adds to its `a` first. -/
def pAt (H M : List Word) (t : Nat) : Word := if t = 0 then 0 else SIGMA0 (varsAt H M (t - 1)).a

/-- The working variables in the registers before round `t`. -/
structure RegsAt (H M : List Word) (t : Nat) (r : Regs) : Prop where
  ha : r.get (varReg t 0) = ((varsAt H M t).a - pAt H M t).setWidth 64
  hb : r.get (varReg t 1) = (varsAt H M t).b.setWidth 64
  hc : r.get (varReg t 2) = (varsAt H M t).c.setWidth 64
  hd : r.get (varReg t 3) = (varsAt H M t).d.setWidth 64
  he : r.get (varReg t 4) = (varsAt H M t).e.setWidth 64
  hf : r.get (varReg t 5) = (varsAt H M t).f.setWidth 64
  hg : r.get (varReg t 6) = (varsAt H M t).g.setWidth 64
  hh : r.get (varReg t 7) = (varsAt H M t).h.setWidth 64
  hp : r.rbp = (pAt H M t).setWidth 64
  hz : r.get (tZ t) = ((varsAt H M t).b ^^^ (varsAt H M t).c).setWidth 64

theorem round_fields (v : Vars) (k w : Word) :
    (round v k w).a = v.h + SIGMA1 v.e + Ch v.e v.f v.g + (w + k) + SIGMA0 v.a + Maj v.a v.b v.c ∧
    (round v k w).b = v.a ∧ (round v k w).c = v.b ∧ (round v k w).d = v.c ∧
    (round v k w).e = v.d + (v.h + SIGMA1 v.e + Ch v.e v.f v.g + (w + k)) ∧
    (round v k w).f = v.e ∧ (round v k w).g = v.f ∧ (round v k w).h = v.g := by
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩ <;> simp only [Spec.SHA256.round] <;> abel

/-- One round on the register state, in terms of the specification. -/
theorem round_regs (H M : List Word) (hM : M.length = 16) (L t : Nat) (hL : L < 2) (ht : t < 64)
    (sp : Addr) (rest : List Region) (s : State) (hr : RegsAt H M t s.gpr)
    (hwk : s.mem.readW (sp + BitVec.ofNat 64 (wkOff L t)) 32 = Wt M t + K[t]!)
    (hrsp : s.gpr.rsp = sp) (hwr : s.wr = ⟨sp, 560⟩ :: rest) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RegsAt H M (t + 1) q.1.gpr ∧
      q.1.gpr.rsp = s.gpr.rsp ∧ q.1.gpr.rdi = s.gpr.rdi ∧ q.1.gpr.rsi = s.gpr.rsi ∧
      q.1.gpr.rdx = s.gpr.rdx ∧ q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  obtain ⟨p1, hp1, post⟩ := round_exec L t hL ht (varsAt H M t) (pAt H M t) (Wt M t + K[t]!) sp rest s
    ⟨hr.ha, hr.hb, hr.hc, hr.hd, hr.he, hr.hf, hr.hg, hr.hh, hr.hp, hr.hz, hwk, hrsp, hwr⟩
  simp only [RoundPost] at post
  obtain ⟨ra, rb, rc, rd, re, rf, rg, rh, rp, rz, rsp', rdi', rsi', rdx', vec', mem', rd', wr', lab'⟩ := post
  have hv := varsAt_succ H M hM t ht
  have hp : pAt H M (t + 1) = SIGMA0 (varsAt H M t).a := by simp [pAt]
  obtain ⟨fa, fb, fc, fd, fe, ff, fg, fh⟩ := round_fields (varsAt H M t) K[t]! (Wt M t)
  refine ⟨p1, hp1, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rsp', rdi', rsi', rdx', vec', mem', rd', wr', lab'⟩ <;>
    (try rw [hv]) <;> (try rw [hp])
  · rw [fa]; exact ra
  · rw [fb]; exact rb
  · rw [fc]; exact rc
  · rw [fd]; exact rd
  · rw [fe]; exact re
  · rw [ff]; exact rf
  · rw [fg]; exact rg
  · rw [fh]; exact rh
  · exact rp
  · rw [fb, fc]; exact rz

/-- The invariant of lane 0 before round `t`. -/
structure L0Inv (s0 : State) (H MA : List Word) (WB : Nat → Word) (sp : Addr) (rest : List Region)
    (t : Nat) (s : State) : Prop where
  regs : RegsAt H MA t s.gpr
  buf : BufInv (Wt MA) WB s.mem sp (min (t / 4 + 4) 16)
  win : t < 48 → WinInv (Wt MA) WB t s
  m10 : s.getV .y10 = maskV shuf00BA
  m11 : s.getV .y11 = maskV shufDC00
  y12 : s.getV .y12 = s0.getV .y12
  rsp : s.gpr.rsp = sp
  rdi : s.gpr.rdi = s0.gpr.rdi
  rsi : s.gpr.rsi = s0.gpr.rsi
  rdx : s.gpr.rdx = s0.gpr.rdx
  mem : Mem.Agree s0.mem s.mem ⟨sp, 512⟩
  rd : s.rd = s0.rd
  wr : s.wr = ⟨sp, 560⟩ :: rest
  labels : s.labels = s0.labels

theorem WinInv.of_vec {WA WB : Nat → Word} {t : Nat} {s s' : State} (h : WinInv WA WB t s)
    (hv : s'.vec = s.vec) : WinInv WA WB t s' := by
  unfold WinInv State.getV at *; rw [hv]; exact h

theorem l0_step (s0 : State) (H MA : List Word) (hM : MA.length = 16) (WB : Nat → Word) (hRB : Recur WB)
    (sp : Addr) (rest : List Region) (hk : KFacts s0 sp) (t : Nat) (ht : t < 64) (s : State)
    (h : L0Inv s0 H MA WB sp rest t s) :
    ∃ q, execBlock isa (lane0Round t) s = some q ∧ L0Inv s0 H MA WB sp rest (t + 1) q.1 := by
  have hwk : s.mem.readW (sp + BitVec.ofNat 64 (wkOff 0 t)) 32 = Wt MA t + K[t]! := by
    have := h.buf t (by omega) 0 (by decide); simpa [WL] using this
  obtain ⟨p1, hp1, hr1, rsp1, rdi1, rsi1, rdx1, vec1, mem1, rd1, wr1, lab1⟩ :=
    round_regs H MA hM 0 t (by decide) ht sp rest s h.regs hwk h.rsp h.wr
  have gv : ∀ v, p1.1.getV v = s.getV v := fun v => by simp only [State.getV, vec1]
  rw [lane0Round, execBlock_append, hp1, Option.bind_some]
  by_cases h48 : t < 48
  · rw [if_pos h48]
    have hbuf : BufInv (Wt MA) WB p1.1.mem sp (t / 4 + 4) := by
      rw [mem1, ← Nat.min_eq_left (show t / 4 + 4 ≤ 16 by omega)]; exact h.buf
    obtain ⟨q, hq, hf, hmem, hbuf', hwin'⟩ := sched_step (Wt MA) WB (Wt_recur MA) hRB sp rest s0 hk t h48 p1.1
      ((h.win h48).of_vec vec1) hbuf (by rw [gv]; exact h.m10) (by rw [gv]; exact h.m11)
      (by rw [rsp1]; exact h.rsp) (by rw [wr1]; exact h.wr) (by rw [rd1]; exact h.rd)
      (by rw [lab1]; exact h.labels) (by rw [mem1]; exact h.mem)
    rw [hq]
    obtain ⟨g1, -, -, -, -, rd2, wr2, lab2, -⟩ := id hf
    refine ⟨_, rfl, ?_⟩
    refine ⟨g1 ▸ hr1, ?_, hwin', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, ?_, ?_, ?_⟩
    · rw [Nat.min_eq_left (show (t + 1) / 4 + 4 ≤ 16 by omega)]; exact hbuf'
    · rw [hf.high _ (by simp), gv]; exact h.m10
    · rw [hf.high _ (by simp), gv]; exact h.m11
    · rw [hf.high _ (by simp), gv]; exact h.y12
    · rw [g1, rsp1]; exact h.rsp
    · rw [g1, rdi1]; exact h.rdi
    · rw [g1, rsi1]; exact h.rsi
    · rw [g1, rdx1]; exact h.rdx
    · rw [rd2, rd1]; exact h.rd
    · rw [wr2, wr1]; exact h.wr
    · rw [lab2, lab1]; exact h.labels
  · rw [if_neg h48]
    refine ⟨_, rfl, ⟨hr1, ?_, fun h' => absurd h' (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [mem1, Nat.min_eq_right (show 16 ≤ (t + 1) / 4 + 4 by omega)]
      have hb := h.buf
      rw [Nat.min_eq_right (show 16 ≤ t / 4 + 4 by omega)] at hb
      exact hb
    · rw [gv]; exact h.m10
    · rw [gv]; exact h.m11
    · rw [gv]; exact h.y12
    · rw [rsp1]; exact h.rsp
    · rw [rdi1]; exact h.rdi
    · rw [rsi1]; exact h.rsi
    · rw [rdx1]; exact h.rdx
    · rw [mem1]; exact h.mem
    · rw [rd1]; exact h.rd
    · rw [wr1]; exact h.wr
    · rw [lab1]; exact h.labels

end CC.X86.SHA256Avx2
