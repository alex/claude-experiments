import ClaudeCrypto.X86.SHA256.Avx2Vec
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.Spec.SHA256Lemmas

/-! # AVX2 SHA-256: the vectorized message schedule (abstract slice lemmas) -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

/-- Word `n` of the schedule of the lane that dword `i` belongs to. -/
def sel (WA WB : Nat → Word) (i n : Nat) : Word := if i < 4 then WA n else WB n

/-- `x` holds words `4k … 4k+3` of both schedules. -/
def HoldsGroup (x : BitVec 256) (WA WB : Nat → Word) (k : Nat) : Prop :=
  ∀ i < 8, lane 32 x i = sel WA WB i (4 * k + i % 4)

/-- After quarter 0 of group `g`: `W[n-16] + W[n-7] + σ₀(W[n-15])` for `n = 4g + i%4`. -/
def part0 (WA WB : Nat → Word) (g i : Nat) : Word :=
  sel WA WB i (4 * g + i % 4 - 16) + sel WA WB i (4 * g + i % 4 - 7) +
    sigma0 (sel WA WB i (4 * g + i % 4 - 15))

/-- The schedule recurrence. -/
def Recur (W : Nat → Word) : Prop :=
  ∀ n, 16 ≤ n → W n = W (n - 16) + W (n - 7) + sigma0 (W (n - 15)) + sigma1 (W (n - 2))

/-- The context the schedule slices need. -/
structure SliceCtx (g : Nat) (WA WB : Nat → Word) (s : State) : Prop where
  x1 : HoldsGroup (s.getV (ymm ((g + 1) % 4))) WA WB (g - 3)
  x2 : HoldsGroup (s.getV (ymm ((g + 2) % 4))) WA WB (g - 2)
  x3 : HoldsGroup (s.getV (ymm ((g + 3) % 4))) WA WB (g - 1)
  m10 : s.getV .y10 = maskV shuf00BA
  m11 : s.getV .y11 = maskV shufDC00

/-- A slice changes only `ymm[g%4]` and the scratch registers `ymm4–ymm7`. -/
def SliceFrame (g : Nat) (s s' : State) : Prop :=
  s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of ∧
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.labels = s.labels ∧
  ∀ v : VReg, v ≠ ymm (g % 4) → v ≠ .y4 → v ≠ .y5 → v ≠ .y6 → v ≠ .y7 → s'.getV v = s.getV v

set_option maxHeartbeats 20000000

set_option hygiene false in
macro "slice_frame_tac" : tactic => `(tactic| (
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro v h0 h4 h5 h6 h7
  cases v <;> simp_all [ymm, VRegs.get, VRegs.set]))

theorem slice0_exec (g : Nat) (hg1 : 4 ≤ g) (hg : g < 16) (WA WB : Nat → Word) (s : State)
    (hc : SliceCtx g WA WB s) (h0 : HoldsGroup (s.getV (ymm (g % 4))) WA WB (g - 4)) :
    ∃ q, execBlock isa (schedSlice g 0) s = some q ∧ SliceFrame g s q.1 ∧ q.1.mem = s.mem ∧
      ∀ i < 8, lane 32 (q.1.getV (ymm (g % 4))) i = part0 WA WB g i := by
  obtain ⟨x1, x2, x3, -, -⟩ := hc
  interval_cases g
  all_goals
    simp only [schedSlice, ymm, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at x1 x2 x3 h0 ⊢
    simp only [execBlock, isa, exec, Instr.sz, execW, execV, State.getV, State.setV, VRegs.get,
      VRegs.set, readVSrc, Option.map_some, Option.bind_some, addrs, List.map_nil, List.nil_append]
    refine ⟨_, rfl, by slice_frame_tac, rfl, ?_⟩
    intro i hi
    simp only [HoldsGroup, State.getV, VRegs.get] at x1 x2 x3 h0
    interval_cases i <;>
      simp (config := { decide := true }) only [VRegs.get, lane_vpaddd, lane_vpxor, lane_vpsrld,
        lane_vpslld, lane_vpalignr4, x1, x2, x3, h0, part0, sel, reduceIte, Nat.reduceMod, Nat.reduceAdd,
        Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff, sigma0_shifts]

/-- After quarter 1: dwords 0,1 of each lane are final. -/
def part1 (WA WB : Nat → Word) (g i : Nat) : Word :=
  if i % 4 < 2 then sel WA WB i (4 * g + i % 4) else part0 WA WB g i

theorem slice1_exec (g : Nat) (hg1 : 4 ≤ g) (hg : g < 16) (WA WB : Nat → Word) (hRA : Recur WA) (hRB : Recur WB)
    (s : State) (hc : SliceCtx g WA WB s)
    (h0 : ∀ i < 8, lane 32 (s.getV (ymm (g % 4))) i = part0 WA WB g i) :
    ∃ q, execBlock isa (schedSlice g 1) s = some q ∧ SliceFrame g s q.1 ∧ q.1.mem = s.mem ∧
      ∀ i < 8, lane 32 (q.1.getV (ymm (g % 4))) i = part1 WA WB g i := by
  obtain ⟨-, -, x3, m10, -⟩ := hc
  interval_cases g
  all_goals
    simp only [schedSlice, ymm, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at x3 h0 ⊢
    simp only [execBlock, isa, exec, Instr.sz, execW, execV, State.getV, State.setV, VRegs.get,
      VRegs.set, readVSrc, Option.map_some, Option.bind_some, addrs, List.map_nil, List.nil_append]
    refine ⟨_, rfl, by slice_frame_tac, rfl, ?_⟩
    intro i hi
    simp only [HoldsGroup, State.getV, VRegs.get] at x3 h0 m10
    rw [m10, lane_vpaddd _ _ _ hi, h0 _ hi]
    interval_cases i <;>
      simp (config := { decide := true }) only [VRegs.get, lane_vpaddd, lane_vpxor, lane_vpsrld,
        lane_vpsrlq, lane_vpshufd, lane_shuf00BA, lane64_eq, x3, part0, part1, sel, reduceIte,
        Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
        Nat.reduceDiv, Nat.reducePow, sigma1_shifts, BitVec.add_zero] <;>
      first
        | rfl
        | (simp only [add_zero])
        | ((conv_rhs => rw [hRA _ (by decide)]) <;>
           simp only [part0, sel, reduceIte, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
             Nat.reduceLT])
        | ((conv_rhs => rw [hRB _ (by decide)]) <;>
           simp only [part0, sel, reduceIte, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
             Nat.reduceLT])

theorem slice2_exec (g : Nat) (hg1 : 4 ≤ g) (hg : g < 16) (WA WB : Nat → Word) (hRA : Recur WA) (hRB : Recur WB)
    (s : State) (m11 : s.getV .y11 = maskV shufDC00)
    (h1 : ∀ i < 8, lane 32 (s.getV (ymm (g % 4))) i = part1 WA WB g i) :
    ∃ q, execBlock isa (schedSlice g 2) s = some q ∧ SliceFrame g s q.1 ∧ q.1.mem = s.mem ∧
      HoldsGroup (q.1.getV (ymm (g % 4))) WA WB g := by
  have e : ∀ i < 8, lane 32 (s.getV (ymm (g % 4))) i =
      if i % 4 < 2 then sel WA WB i (4 * g + i % 4) else part0 WA WB g i := h1
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have e6 := e 6 (by decide); have e7 := e 7 (by decide)
  clear e h1
  interval_cases g
  all_goals
    simp only [schedSlice, ymm, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, part0, sel, reduceIte,
      Nat.reduceMul, Nat.reduceLT, Nat.reduceDiv] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
    simp only [execBlock, isa, exec, Instr.sz, execW, execV, State.getV, State.setV, VRegs.get,
      VRegs.set, readVSrc, Option.map_some, addrs, List.map_nil, List.nil_append]
    refine ⟨_, rfl, by slice_frame_tac, rfl, ?_⟩
    intro i hi
    simp only [State.getV, VRegs.get] at e0 e1 e2 e3 e4 e5 e6 e7 m11
    rw [m11]
    interval_cases i <;>
      simp (config := { decide := true }) only [VRegs.get, lane_vpaddd, lane_vpxor, lane_vpsrld,
        lane_vpsrlq, lane_vpshufd, lane_shufDC00, lane64_eq, e0, e1, e2, e3, e4, e5, e6, e7, sel, reduceIte,
        Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
        Nat.reduceDiv, Nat.reducePow, sigma1_shifts, BitVec.add_zero] <;>
      first
        | rfl
        | (simp only [add_zero])
        | ((conv_rhs => rw [hRA _ (by decide)]) <;>
           simp only [Nat.reduceSub])
        | ((conv_rhs => rw [hRB _ (by decide)]) <;>
           simp only [Nat.reduceSub])

/-- The address of group `g` of the `K` table. -/
def kAddr (s : State) (g : Nat) : Addr := s.labels kLabel + BitVec.ofNat 64 (32 * g)

theorem slice3_exec (g : Nat) (hg : g < 16) (sp : Addr) (rest : List Region) (s : State)
    (hK : InRegions s.rd (kAddr s g) 32) (hrsp : s.gpr.rsp = sp) (hwr : s.wr = ⟨sp, 560⟩ :: rest) :
    ∃ q, execBlock isa (schedSlice g 3) s = some q ∧ SliceFrame g s q.1 ∧
      q.1.getV (ymm (g % 4)) = s.getV (ymm (g % 4)) ∧
      q.1.mem = s.mem.writeW (sp + BitVec.ofNat 64 (32 * g))
        (vpadddV (s.getV (ymm (g % 4))) (s.mem.readW (kAddr s g) 256)) := by
  have hst : InRegions s.wr (sp + BitVec.ofNat 64 (32 * g)) 32 := by
    rw [hwr, inRegions_cons]; left
    exact Region.contains_offset _ _ _ _ (by omega) (by decide)
  have hld : InRegions (s.rd ++ s.wr) (kAddr s g) 32 := by
    rw [inRegions_append]; left; exact hK
  simp only [kAddr] at hld ⊢
  have hj : g % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [schedSlice]
  generalize g % 4 = j at hj ⊢
  simp only [execBlock, isa, exec, Instr.sz, execW, execV, readVSrc, State.loadW, State.storeW,
    State.ea, ripAt, rspAt, State.getReg, Regs.get, hrsp, BitVec.ofInt_natCast, Nat.reduceDiv, hld, hst,
    ite_true, Option.map_some, addrs, State.setV]
  interval_cases j <;> simp only [ymm, State.getV, State.setV, VRegs.get, VRegs.set] <;>
    refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl, rfl⟩ <;>
    intro v h0 h4 h5 h6 h7 <;> cases v <;> first | rfl | exact absurd rfl h0 | exact absurd rfl h4

end CC.X86.SHA256Avx2
