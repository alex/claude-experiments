import ClaudeCrypto.Limb.Basic
import ClaudeCrypto.Framework.Compile
import ClaudeCrypto.Arm.StateLemmas

/-!
# Compiling the limb IR to AArch64

IR register `v` is the AArch64 register `X<v>` (`X0`–`X14`, all caller-saved
under AAPCS64; IR register 0, the `mulx` multiplicand, is `X0`).  `X16` (IP0)
is a scratch register, used only to materialize offsets and immediates that
do not fit the instruction encodings.  `SP`, `X15`, `X17`–`X30` and the
vector registers are never written.

The IR carry flag has the x86 convention (borrow after a subtraction); the
AArch64 C flag holds NOT(borrow) after `subs`/`sbcs`, so `Rel` relates the IR
carry `c` to `C = c` after additions and `C = !c` after subtractions (the IR's
`sub` mode flag records which).  IR `mask` (all ones iff the last subtraction
borrowed) is `csetm Xd, lo`.  Branches on `r = 0` become `cbz`/`cbnz`.

`sim` proves the simulation obligations of `Framework/Compile.lean`, so every
proven IR program yields proven AArch64 code.
-/

namespace CC.Limb.Arm

open CC.Arm

/-- The AArch64 register holding each IR register. -/
def phys : Var → XReg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6
  | 7 => .x7 | 8 => .x8 | 9 => .x9 | 10 => .x10 | 11 => .x11 | 12 => .x12 | 13 => .x13 | 14 => .x14

/-- The scratch register (IP0) for immediates that do not fit an encoding. -/
abbrev scratch : XReg := .x16

theorem phys_inj (a b : Var) : phys a = phys b ↔ a = b := by
  constructor
  · revert a b; decide
  · rintro rfl; rfl

theorem phys_ne_scratch (a : Var) : phys a ≠ scratch := by revert a; decide

/-! ## Materializing constants -/

/-- The 16-bit chunk `k` of `v`. -/
def chunk (v : BitVec 64) (k : Nat) : BitVec 16 := v.extractLsb' (16 * k) 16

/-- `movk r, #chunk, lsl #(16k)`, omitted if the chunk is zero. -/
def movkIf (r : XReg) (v : BitVec 64) (k : Nat) : List Arm.Instr :=
  if chunk v k = 0 then [] else [.movk r (chunk v k) k]

/-- `r := v` by `movz` and up to three `movk`s. -/
def movImm (r : XReg) (v : BitVec 64) : List Arm.Instr :=
  .movz r (chunk v 0) 0 :: (movkIf r v 1 ++ movkIf r v 2 ++ movkIf r v 3)

/-- `d := n + off`: an immediate `add` if `off` is encodable, else via the scratch register. -/
def addOff (d n : XReg) (off : Nat) : List Arm.Instr :=
  if off < 4096 then [.addi d n off] else movImm scratch (BitVec.ofNat 64 off) ++ [.addr d n scratch]

/-- `d := n - off`. -/
def subOff (d n : XReg) (off : Nat) : List Arm.Instr :=
  if off < 4096 then [.subi d n off] else movImm scratch (BitVec.ofNat 64 off) ++ [.subr d n scratch]

/-- `off` is encodable as the unsigned offset of a 64-bit `ldr`/`str`. -/
def ImmOff (off : Nat) : Prop := off % 8 = 0 ∧ off < 32768

instance (off : Nat) : Decidable (ImmOff off) := inferInstanceAs (Decidable (_ ∧ _))

/-- `t := [b + off]` (64-bit). -/
def ldOff (t b : XReg) (off : Nat) : List Arm.Instr :=
  if ImmOff off then [.ldr t b off] else movImm scratch (BitVec.ofNat 64 off) ++ [.ldrr t b scratch]

/-- `[b + off] := t` (64-bit). -/
def stOff (t b : XReg) (off : Nat) : List Arm.Instr :=
  if ImmOff off then [.str t b off] else movImm scratch (BitVec.ofNat 64 off) ++ [.strr t b scratch]

/-! ## The compiler -/

def instr : Limb.Instr → List Arm.Instr
  | .mov d s => [.mov (phys d) (phys s)]
  | .movi d v => movImm (phys d) v
  | .lea d l off => .adr (phys d) l :: (if off = 0 then [] else addOff (phys d) (phys d) off)
  | .ld d b off => ldOff (phys d) (phys b) off
  | .ldbe d b off => ldOff (phys d) (phys b) off ++ [.rev (phys d) (phys d)]
  | .st b off s => stOff (phys s) (phys b) off
  | .mulx hi lo b => [.mul (phys lo) (phys 0) (phys b), .umulh (phys hi) (phys 0) (phys b)]
  | .add d s => [.adds (phys d) (phys d) (phys s)]
  | .adc d s => [.adcs (phys d) (phys d) (phys s)]
  | .sub d s => [.subs (phys d) (phys d) (phys s)]
  | .sbb d s => [.sbcs (phys d) (phys d) (phys s)]
  | .mask d => [.csetm (phys d) .lo]
  | .and d s => [.and (phys d) (phys d) (phys s)]
  | .or d s => [.orr (phys d) (phys d) (phys s)]
  | .xor d s => [.eor (phys d) (phys d) (phys s)]
  | .shr d n => [.lsr (phys d) (phys d) n]
  | .shl d n => [.lsl (phys d) (phys d) n]
  | .addi d n => addOff (phys d) (phys d) n
  | .subi d n => subOff (phys d) (phys d) n
  | .clrc => []

def cond : Limb.Cond → List Arm.Instr × Arm.Cond
  | .eqz v => ([], .cbz (phys v))
  | .nez v => ([], .cbnz (phys v))

def compiler : Compiler Limb.isa Arm.isa := ⟨instr, cond⟩

/-- The simulation relation.  `f` is the machine state on entry: `SP`, the vector
registers and every general-purpose register other than `X0`–`X14` (the IR
registers) and `X16` (the scratch register) keep their values from `f`. -/
structure Rel (f : Arm.State) (s : Limb.State) (t : Arm.State) : Prop where
  regs : ∀ v, t.getX (phys v) = s.r v
  /-- the C flag is the IR carry, or its negation after a subtraction -/
  cf : ∀ c, s.cf = some c → t.cf = some (if s.sub then !c else c)
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  labels : t.labels = s.labels
  sp : t.sp = f.sp
  v : t.v = f.v
  frame : ∀ r, (∀ v, phys v ≠ r) → r ≠ scratch → t.getX r = f.getX r

/-! ## Lemmas -/

theorem XRegs.set_set (g : XRegs) (r : XReg) (x y : BitVec 64) : (g.set r x).set r y = g.set r y := by
  cases r <;> rfl

theorem setX_setX (t : Arm.State) (r : XReg) (x y : BitVec 64) : (t.setX r x).setX r y = t.setX r y := by
  simp only [State.setX, XRegs.set_set]

theorem getX_setX_phys (t : Arm.State) (d v : Var) (x : BitVec 64) :
    (t.setX (phys d) x).getX (phys v) = if v = d then x else t.getX (phys v) := by
  rw [State.getX_setX]; simp only [phys_inj]

theorem getX_setX_scratch_phys (t : Arm.State) (v : Var) (x : BitVec 64) :
    (t.setX scratch x).getX (phys v) = t.getX (phys v) :=
  State.getX_setX_ne _ _ _ _ (phys_ne_scratch v)

theorem Rel.setX {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (d : Var) (x : BitVec 64)
    (cf : Option Bool) (sub : Bool) (hcf : ∀ c, cf = some c → t.cf = some (if sub then !c else c)) :
    Rel f { s.set d x with cf := cf, sub := sub } (t.setX (phys d) x) := by
  refine ⟨fun v => ?_, hcf, h.mem, h.rd, h.wr, h.labels, h.sp, h.v, fun r hr hs => ?_⟩
  · rw [getX_setX_phys]
    simp only [Limb.State.set, Function.update_apply]
    split_ifs <;> [rfl; exact h.regs v]
  · rw [State.getX_setX_ne _ _ _ _ (Ne.symm (hr d))]; exact h.frame r hr hs

/-- Writing an IR register, keeping the IR carry. -/
theorem Rel.set {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (d : Var) (x : BitVec 64) :
    Rel f (s.set d x) (t.setX (phys d) x) :=
  h.setX d x s.cf s.sub h.cf

/-- Writing an IR register, forgetting the IR carry. -/
theorem Rel.setNone {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (d : Var) (x : BitVec 64) :
    Rel f { s.set d x with cf := none } (t.setX (phys d) x) :=
  h.setX d x none s.sub (fun _ hc => by cases hc)

theorem Rel.setNZCV {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (d : Var) (x : BitVec 64)
    (c sub : Bool) (r : BitVec 64 × Bool × Bool × Bool × Bool) (hx : r.1 = x)
    (hc : r.2.2.2.1 = if sub then !c else c) :
    Rel f { s.set d x with cf := some c, sub := sub } (t.setNZCV (phys d) r) := by
  refine ⟨fun v => ?_, fun c' hc' => ?_, h.mem, h.rd, h.wr, h.labels, h.sp, h.v, fun r' hr' hs => ?_⟩
  · simp only [State.setNZCV, getX_setX_phys, hx, Limb.State.set, Function.update_apply]
    split_ifs <;> [rfl; exact h.regs v]
  · cases hc'; show some r.2.2.2.1 = _; rw [hc]
  · simp only [State.setNZCV]
    rw [State.getX_setX_ne _ _ _ _ (Ne.symm (hr' d))]; exact h.frame r' hr' hs

theorem Rel.setScratch {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (x : BitVec 64) :
    Rel f s (t.setX scratch x) := by
  refine ⟨fun v => ?_, h.cf, h.mem, h.rd, h.wr, h.labels, h.sp, h.v, fun r hr hs => ?_⟩
  · rw [getX_setX_scratch_phys]; exact h.regs v
  · rw [State.getX_setX_ne _ _ _ _ hs]; exact h.frame r hr hs

/-! ### `AddWithCarry` -/

theorem awc_res (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).1 = a + b + (BitVec.ofBool c).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  cases c <;> simp [addWithCarry, BitVec.toNat_add, Nat.add_mod]

theorem awc_carry (a b : BitVec 64) (c : Bool) : (addWithCarry a b c).2.2.2.1 = carryOut a b c := rfl

theorem awc_sub_res (a b : BitVec 64) (c : Bool) :
    (addWithCarry a (~~~b) (!c)).1 = a - b - (BitVec.ofBool c).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  cases c <;> simp [addWithCarry, BitVec.toNat_sub, BitVec.toNat_not] <;> omega

theorem awc_sub_carry (a b : BitVec 64) (c : Bool) :
    (addWithCarry a (~~~b) (!c)).2.2.2.1 = !borrowOut a b c := by
  have hb : b.toNat < 18446744073709551616 := b.isLt
  have hn : (~~~b).toNat = 18446744073709551615 - b.toNat := BitVec.toNat_not
  rw [Bool.eq_iff_iff]
  cases c <;> simp only [addWithCarry, borrowOut, hn, Nat.ble_eq, Nat.blt_eq, Bool.not_true,
    Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.not_eq_true', Nat.reducePow, Bool.eq_false_iff,
    ne_eq] <;> omega

theorem awc_subs_res (a b : BitVec 64) : (addWithCarry a (~~~b) true).1 = a - b := by
  simpa using awc_sub_res a b false

theorem awc_subs_carry (a b : BitVec 64) : (addWithCarry a (~~~b) true).2.2.2.1 = !borrowOut a b false :=
  awc_sub_carry a b false

/-! ### `movz`/`movk` -/

/-- `x` agrees with `v` on the low `n` bits and is zero above. -/
def Low (v x : BitVec 64) (n : Nat) : Prop := ∀ i, x.getLsbD i = (decide (i < n) && v.getLsbD i)

theorem ofNat_ffff : BitVec.ofNat 64 0xFFFF = (BitVec.allOnes 16).setWidth 64 := by decide

theorem low_movz (v : BitVec 64) : Low v ((chunk v 0).setWidth 64 <<< (16 * 0)) 16 := by
  intro i
  simp only [chunk, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases h : i < 16
  · simp [h, show i < 64 by omega]
  · simp [h]

theorem low_movk (v x : BitVec 64) (k : Nat) (hk : k < 4) (h : Low v x (16 * k)) :
    Low v (if chunk v k = 0 then x else movkVal x (chunk v k) (16 * k)) (16 * (k + 1)) := by
  intro i
  split_ifs with hc
  · rw [h i]
    by_cases h1 : i < 16 * k
    · simp [h1, show i < 16 * (k + 1) by omega]
    · by_cases h2 : i < 16 * (k + 1)
      · have := congrArg (fun y => y.getLsbD (i - 16 * k)) hc
        simp only [chunk, BitVec.getLsbD_extractLsb'] at this
        simp only [show i - 16 * k < 16 by omega, decide_true, Bool.true_and,
          show 16 * k + (i - 16 * k) = i by omega] at this
        simp [h1, h2, this]
      · simp [h1, h2]
  · simp only [movkVal, ofNat_ffff, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, chunk,
      BitVec.getLsbD_extractLsb', h i]
    by_cases h1 : i < 16 * k
    · simp [h1, show i < 16 * (k + 1) by omega]
      intro hv; exact BitVec.lt_of_getLsbD hv
    · by_cases h2 : i < 16 * (k + 1)
      · simp [h1, h2, show i - 16 * k < 16 by omega, show i < 64 by omega,
          show 16 * k + (i - 16 * k) = i by omega]
        intro; omega
      · by_cases h3 : i < 64
        · simp [h1, h2, h3, show ¬ i - 16 * k < 16 by omega]
        · simp [h1, h2, h3]

theorem low_64 {v x : BitVec 64} (h : Low v x 64) : x = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [h i]; simp [hi]

theorem movkIf_exec (t : Arm.State) (r : XReg) (v x : BitVec 64) (k : Nat) (hk : k < 4)
    (h : Low v x (16 * k)) :
    ∃ x', execBlock Arm.isa (movkIf r v k) (t.setX r x) = some (t.setX r x', []) ∧
      Low v x' (16 * (k + 1)) := by
  refine ⟨_, ?_, low_movk v x k hk h⟩
  unfold movkIf
  split_ifs
  · rfl
  · simp only [execBlock, Arm.isa, CC.Arm.exec, State.getX_setX_same, setX_setX, CC.Arm.addrs, List.map_nil,
      Option.map_some, List.append_nil]

theorem execBlock_append_some {l₁ l₂ : List Arm.Instr} {t t₁ t₂ : Arm.State}
    (h₁ : execBlock Arm.isa l₁ t = some (t₁, [])) (h₂ : execBlock Arm.isa l₂ t₁ = some (t₂, [])) :
    execBlock Arm.isa (l₁ ++ l₂) t = some (t₂, []) := by
  rw [execBlock_append, h₁]; simp [h₂]

theorem movImm_exec (t : Arm.State) (r : XReg) (v : BitVec 64) :
    execBlock Arm.isa (movImm r v) t = some (t.setX r v, []) := by
  obtain ⟨x1, h1, l1⟩ := movkIf_exec t r v _ 1 (by omega) (low_movz v)
  obtain ⟨x2, h2, l2⟩ := movkIf_exec t r v _ 2 (by omega) l1
  obtain ⟨x3, h3, l3⟩ := movkIf_exec t r v _ 3 (by omega) l2
  have := low_64 l3; subst this
  have h0 : execBlock Arm.isa [.movz r (chunk x3 0) 0] t =
      some (t.setX r ((chunk x3 0).setWidth 64 <<< (16 * 0)), []) := rfl
  exact execBlock_append_some h0 (execBlock_append_some (execBlock_append_some h1 h2) h3)

/-! ## Simulation -/

theorem exec_ofNat_off (t : Arm.State) (off : Nat) :
    execBlock Arm.isa (movImm scratch (BitVec.ofNat 64 off)) t =
      some (t.setX scratch (BitVec.ofNat 64 off), []) := movImm_exec _ _ _

theorem Rel.mem' {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) (m : Mem) :
    Rel f { s with mem := m } { t with mem := m } :=
  ⟨h.regs, h.cf, rfl, h.rd, h.wr, h.labels, h.sp, h.v, h.frame⟩

theorem Rel.forget {f : Arm.State} {s : Limb.State} {t : Arm.State} (h : Rel f s t) :
    Rel f { s with cf := none } t :=
  ⟨h.regs, fun _ hc => (by cases hc), h.mem, h.rd, h.wr, h.labels, h.sp, h.v, h.frame⟩

/-- A single instruction simulating an IR step (the target state `t'` is given by `hR`). -/
theorem sim1 {f t : Arm.State} {s' : Limb.State} (i : Arm.Instr) {t' : Arm.State} (hR : Rel f s' t')
    (h : CC.Arm.exec i t = some t') : ∃ q, execBlock Arm.isa [i] t = some q ∧ Rel f s' q.1 :=
  ⟨(t', (CC.Arm.addrs i t).map Leak.addr), by simp [execBlock, Arm.isa, h], hR⟩

/-- An instruction after materializing `off` in the scratch register. -/
theorem simS {f t : Arm.State} {s' : Limb.State} (off : Nat) (i : Arm.Instr) {t' : Arm.State}
    (hR : Rel f s' t') (h : CC.Arm.exec i (t.setX scratch (BitVec.ofNat 64 off)) = some t') :
    ∃ q, execBlock Arm.isa (movImm scratch (BitVec.ofNat 64 off) ++ [i]) t = some q ∧ Rel f s' q.1 := by
  refine ⟨(t', (CC.Arm.addrs i (t.setX scratch (BitVec.ofNat 64 off))).map Leak.addr), ?_, hR⟩
  rw [execBlock_append, exec_ofNat_off]; simp [execBlock, Arm.isa, h]

theorem sim_app {f t : Arm.State} {s₁ s₂ : Limb.State} {l₁ l₂ : List Arm.Instr}
    (h₁ : ∃ q, execBlock Arm.isa l₁ t = some q ∧ Rel f s₁ q.1)
    (h₂ : ∀ t₁, Rel f s₁ t₁ → ∃ q, execBlock Arm.isa l₂ t₁ = some q ∧ Rel f s₂ q.1) :
    ∃ q, execBlock Arm.isa (l₁ ++ l₂) t = some q ∧ Rel f s₂ q.1 := by
  obtain ⟨q₁, e₁, r₁⟩ := h₁
  obtain ⟨q₂, e₂, r₂⟩ := h₂ q₁.1 r₁
  exact ⟨(q₂.1, q₁.2 ++ q₂.2), by rw [execBlock_append, e₁]; simp [e₂], r₂⟩

theorem ldOff_exec {f : Arm.State} {s : Limb.State} {t : Arm.State} (hr : Rel f s t) (d b : Var) (off : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.r b + BitVec.ofNat 64 off) 8) :
    ∃ q, execBlock Arm.isa (ldOff (phys d) (phys b) off) t = some q ∧
      Rel f (s.set d (s.mem.readW (s.r b + BitVec.ofNat 64 off) 64)) q.1 := by
  unfold ldOff
  split_ifs
  · refine sim1 _ (hr.set d _) ?_
    simp only [CC.Arm.exec, State.loadW, hr.regs, hr.rd, hr.wr, Nat.reduceDiv, hp, ite_true,
      Option.map_some, hr.mem]
  · refine simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _) ?_
    simp only [CC.Arm.exec, State.loadW, getX_setX_scratch_phys, State.getX_setX_same, hr.regs,
      State.setX_rd, State.setX_wr, State.setX_mem, hr.rd, hr.wr, Nat.reduceDiv, hp, ite_true,
      Option.map_some, hr.mem]

theorem stOff_exec {f : Arm.State} {s : Limb.State} {t : Arm.State} (hr : Rel f s t) (x b : Var) (off : Nat)
    (hp : InRegions s.wr (s.r b + BitVec.ofNat 64 off) 8) :
    ∃ q, execBlock Arm.isa (stOff (phys x) (phys b) off) t = some q ∧
      Rel f { s with mem := s.mem.writeW (s.r b + BitVec.ofNat 64 off) (s.r x) } q.1 := by
  unfold stOff
  split_ifs
  · refine sim1 _ (hr.mem' _) ?_
    simp only [CC.Arm.exec, State.storeW, hr.regs, hr.wr, Nat.reduceDiv, hp, ite_true, hr.mem]
  · refine simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).mem' _) ?_
    simp only [CC.Arm.exec, State.storeW, getX_setX_scratch_phys, State.getX_setX_same, hr.regs,
      State.setX_wr, State.setX_mem, hr.wr, Nat.reduceDiv, hp, ite_true, hr.mem]

theorem addOff_exec {f : Arm.State} {s : Limb.State} {t : Arm.State} (hr : Rel f s t) (d : Var) (off : Nat) :
    ∃ q, execBlock Arm.isa (addOff (phys d) (phys d) off) t = some q ∧
      Rel f (s.set d (s.r d + BitVec.ofNat 64 off)) q.1 := by
  unfold addOff
  split_ifs
  · exact sim1 _ (hr.set d _) (by simp only [CC.Arm.exec, hr.regs])
  · exact simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _)
      (by simp only [CC.Arm.exec, getX_setX_scratch_phys, State.getX_setX_same, hr.regs])

theorem subOff_exec {f : Arm.State} {s : Limb.State} {t : Arm.State} (hr : Rel f s t) (d : Var) (off : Nat) :
    ∃ q, execBlock Arm.isa (subOff (phys d) (phys d) off) t = some q ∧
      Rel f (s.set d (s.r d - BitVec.ofNat 64 off)) q.1 := by
  unfold subOff
  split_ifs
  · exact sim1 _ (hr.set d _) (by simp only [CC.Arm.exec, hr.regs])
  · exact simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _)
      (by simp only [CC.Arm.exec, getX_setX_scratch_phys, State.getX_setX_same, hr.regs])

theorem revBytes64_eq (x : BitVec 64) : revBytes64 x = bswap64 x := rfl

theorem set_set (s : Limb.State) (d : Var) (x y : BitVec 64) : (s.set d x).set d y = s.set d y := by
  simp only [Limb.State.set, Function.update_idem]

theorem set_r_self (s : Limb.State) (d : Var) (x : BitVec 64) : (s.set d x).r d = x := by
  simp only [Limb.State.set, Function.update_self]

theorem sim_instr (f : Arm.State) (i : Limb.Instr) (s s' : Limb.State) (t : Arm.State) (hr : Rel f s t)
    (he : Limb.isa.exec i s = some s') :
    ∃ q, execBlock Arm.isa (compiler.instr i) t = some q ∧ Rel f s' q.1 := by
  cases i with
  | mov d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.set d _) (by simp only [CC.Arm.exec, hr.regs])
  | movi d v =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact ⟨_, movImm_exec _ _ _, hr.set d v⟩
  | lea d l off =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    have h1 := sim1 (t := t) (.adr (phys d) l) (hr.set d (s.labels l))
      (by simp only [CC.Arm.exec, hr.labels])
    simp only [compiler, instr]
    split_ifs with h0
    · subst h0
      simpa using h1
    · refine sim_app (l₁ := [.adr (phys d) l]) h1 (fun t₁ hr₁ => ?_)
      have := addOff_exec hr₁ d off
      rwa [set_r_self, set_set] at this
  | ld d b off =>
    simp only [Limb.isa, Limb.exec, Limb.State.load] at he
    split at he
    · rename_i hp
      simp only [Option.map_some, Option.some.injEq] at he; subst he
      exact ldOff_exec hr d b off hp
    · cases he
  | ldbe d b off =>
    simp only [Limb.isa, Limb.exec, Limb.State.load] at he
    split at he
    · rename_i hp
      simp only [Option.map_some, Option.some.injEq] at he; subst he
      refine sim_app (ldOff_exec hr d b off hp) (fun t₁ hr₁ => ?_)
      have hR := hr₁.set d (bswap64 (s.mem.readW (s.r b + BitVec.ofNat 64 off) 64))
      rw [set_set] at hR
      exact sim1 _ hR (by simp only [CC.Arm.exec, hr₁.regs, set_r_self, revBytes64_eq])
    · cases he
  | st b off x =>
    simp only [Limb.isa, Limb.exec, Limb.State.store] at he
    split at he
    · rename_i hp
      simp only [Option.some.injEq] at he; subst he
      exact stOff_exec hr x b off hp
    · cases he
  | mulx hi lo b =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · cases he
    · rename_i hc
      simp only [Option.some.injEq] at he; subst he
      simp only [not_or] at hc
      obtain ⟨-, h0, hb⟩ := hc
      refine sim_app (l₁ := [_]) (l₂ := [_])
        (sim1 _ (hr.set lo (BitVec.ofNat 64 ((s.r 0).toNat * (s.r b).toNat)))
          (by simp only [CC.Arm.exec, hr.regs])) (fun t₁ hr₁ => ?_)
      have e0 := hr₁.regs 0
      have eb := hr₁.regs b
      simp only [Limb.State.set, Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm hb)] at e0 eb
      exact sim1 _ (hr₁.set hi _) (by simp only [CC.Arm.exec, e0, eb])
  | add d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNZCV d _ _ false (addWithCarry (s.r d) (s.r x) false) (by rw [awc_res]; simp)
      (by rw [awc_carry]; rfl)) (by simp only [CC.Arm.exec, hr.regs])
  | sub d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNZCV d _ _ true (addWithCarry (s.r d) (~~~(s.r x)) true) (awc_subs_res _ _)
      (by rw [awc_subs_carry]; rfl)) (by simp only [CC.Arm.exec, hr.regs])
  | adc d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.cf = some c := by simpa [hsub] using hr.cf c hcf
      exact sim1 _ (hr.setNZCV d _ _ false (addWithCarry (s.r d) (s.r x) c) (by rw [awc_res])
        (by rw [awc_carry]; rfl)) (by simp only [CC.Arm.exec, hr.regs, htc, Option.map_some])
    · cases he
  | sbb d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.cf = some (!c) := by simpa [hsub] using hr.cf c hcf
      exact sim1 _ (hr.setNZCV d _ _ true (addWithCarry (s.r d) (~~~(s.r x)) (!c)) (by rw [awc_sub_res])
        (by rw [awc_sub_carry]; rfl)) (by simp only [CC.Arm.exec, hr.regs, htc, Option.map_some])
    · cases he
  | mask d =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.cf = some (!c) := by simpa [hsub] using hr.cf c hcf
      exact sim1 _ (hr.set d _) (by simp only [CC.Arm.exec, condHolds, htc, Option.map_some, Bool.not_not])
    · cases he
  | and d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Arm.exec, hr.regs])
  | or d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Arm.exec, hr.regs])
  | xor d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Arm.exec, hr.regs])
  | shr d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he
      exact sim1 _ (hr.setNone d _) (by simp only [CC.Arm.exec, hr.regs])
    · cases he
  | shl d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he
      exact sim1 _ (hr.setNone d _) (by simp only [CC.Arm.exec, hr.regs])
    · cases he
  | addi d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he
      obtain ⟨q, hq, hrq⟩ := addOff_exec hr d n
      exact ⟨q, hq, hrq.forget⟩
    · cases he
  | subi d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he
      obtain ⟨q, hq, hrq⟩ := subOff_exec hr d n
      exact ⟨q, hq, hrq.forget⟩
    · cases he
  | clrc =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact ⟨(t, []), rfl, hr.forget⟩

theorem sim_cond (f : Arm.State) (c : Limb.Cond) (s : Limb.State) (t : Arm.State) (b : Bool) (hr : Rel f s t)
    (he : Limb.isa.eval c s = some b) :
    ∃ q, execBlock Arm.isa (compiler.cond c).1 t = some q ∧ Rel f s q.1 ∧
      Arm.isa.eval (compiler.cond c).2 q.1 = some b := by
  simp only [Limb.eval] at he
  split at he
  · cases he
  · cases c with
    | eqz v =>
      simp only [Option.some.injEq] at he; subst he
      refine ⟨(t, []), rfl, hr, ?_⟩
      simp only [compiler, cond, Arm.isa, evalCond, hr.regs v]
    | nez v =>
      simp only [Option.some.injEq] at he; subst he
      refine ⟨(t, []), rfl, hr, ?_⟩
      simp only [compiler, cond, Arm.isa, evalCond, hr.regs v]

/-- **The IR-to-AArch64 compiler is correct**: `f` is the machine state on entry,
whose `SP`, vector registers and non-IR general-purpose registers (other than
the scratch `X16`) are preserved. -/
theorem sim (f : Arm.State) : compiler.Sim (Rel f) :=
  ⟨fun i s s' t hr he => sim_instr f i s s' t hr he, fun c s t b hr he => sim_cond f c s t b hr he⟩

end CC.Limb.Arm
