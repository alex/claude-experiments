import ClaudeCrypto.Limb.Basic
import ClaudeCrypto.Framework.Compile
import ClaudeCrypto.Ppc.StateLemmas

/-!
# Compiling the limb IR to ppc64le

## Register mapping

| IR register | 0–9     | 10–14    |
|-------------|---------|----------|
| ppc64le GPR | r3–r12  | r14–r18  |

(`phys v`).  IR register 0, the `mulx` multiplicand, is `r3` (the first
argument register).  `r0` is the scratch register: it materializes offsets
and immediates that do not fit an instruction encoding, and `adr` (for `lea`)
copies the link register into it.  `r0` is never used where the ISA reads
`(RA|0)` as the constant 0 would matter: IR registers are never `r0`, and the
scratch register only appears as `RB` (or `RT`/`RS`).  `r1` (stack pointer),
`r2` (TOC), `r13` (thread pointer), `r19`–`r31`, the link register, CR1–CR7
and all vector/VSX registers are never written; `r14`–`r18` are nonvolatile
under the ELFv2 ABI, so a function wrapper must save and restore them.  CR0 is
written by the compare before each branch.

## Carry

The IR carry flag has the x86 convention (borrow after a subtraction);
`XER.CA` holds NOT(borrow) after `subfc`/`subfe`, so `Rel` relates the IR
carry `c` to `CA = c` after additions and `CA = !c` after subtractions (the
IR's `sub` mode flag records which), exactly as for AArch64's C flag.

* `add d s` is `addc d,d,s`; `adc` is `adde d,d,s`;
* `sub d s` is `subfc d,s,d` (`d - s`); `sbb` is `subfe d,s,d`;
* `mask d` is `subfe d,d,d`: `¬d + d + CA = 2^64 - 1 + CA`, i.e. all ones iff
  `CA = 0` (the subtraction borrowed), and it leaves `CA` unchanged.

Branches on `r = 0` become `cmpldi r,0` followed by `beq`/`bne` (the IR
requires the carry to be undefined at a branch, and CR0 is not the carry).

`sim` proves the simulation obligations of `Framework/Compile.lean`, so every
proven IR program yields proven ppc64le code.
-/

namespace CC.Limb.Ppc

open CC.Ppc

set_option linter.unusedSimpArgs false

/-- The ppc64le register holding each IR register. -/
def phys : Var → GReg
  | 0 => .r3 | 1 => .r4 | 2 => .r5 | 3 => .r6 | 4 => .r7 | 5 => .r8 | 6 => .r9
  | 7 => .r10 | 8 => .r11 | 9 => .r12 | 10 => .r14 | 11 => .r15 | 12 => .r16 | 13 => .r17 | 14 => .r18

/-- The scratch register. -/
abbrev scratch : GReg := .r0

theorem phys_inj (a b : Var) : phys a = phys b ↔ a = b := by
  constructor
  · revert a b; decide
  · rintro rfl; rfl

theorem phys_ne_scratch (a : Var) : phys a ≠ scratch := by revert a; decide

theorem phys_ne_r1 (a : Var) : phys a ≠ .r1 := by revert a; decide

theorem raOr0_phys (t : Ppc.State) (v : Var) : t.raOr0 (phys v) = t.getG (phys v) := by
  unfold State.raOr0
  split
  · exact absurd ‹_› (phys_ne_scratch v)
  · rfl

/-! ## Materializing constants -/

/-- The 16-bit chunk `k` of `v`, as a number. -/
def chunk (v : BitVec 64) (k : Nat) : Nat := v.toNat / 2 ^ (16 * k) % 2 ^ 16

/-- `r := v`: `li r,v` for small values, else
`li r,0; oris r,r,c3; ori r,r,c2; sldi r,r,32; oris r,r,c1; ori r,r,c0`. -/
def movImm (r : GReg) (v : BitVec 64) : List Ppc.Instr :=
  if v.toNat < 32768 then [.addi r .r0 v.toNat]
  else [.addi r .r0 0, .oris r r (chunk v 3), .ori r r (chunk v 2), .rldicr r r 32 31,
    .oris r r (chunk v 1), .ori r r (chunk v 0)]

/-- `d := d + off`. -/
def addOff (d : GReg) (off : Nat) : List Ppc.Instr :=
  if off < 32768 then [.addi d d off] else movImm scratch (BitVec.ofNat 64 off) ++ [.add d d scratch]

/-- `off` is encodable as the displacement of a DS-form `ld`/`std`. -/
def DsOff (off : Nat) : Prop := off % 4 = 0 ∧ off < 32768

instance (off : Nat) : Decidable (DsOff off) := inferInstanceAs (Decidable (_ ∧ _))

/-- `t := [b + off]` (64-bit). -/
def ldOff (t b : GReg) (off : Nat) : List Ppc.Instr :=
  if DsOff off then [.ld t b off] else movImm scratch (BitVec.ofNat 64 off) ++ [.ldx t b scratch]

/-- `[b + off] := x` (64-bit). -/
def stOff (x b : GReg) (off : Nat) : List Ppc.Instr :=
  if DsOff off then [.std x b off] else movImm scratch (BitVec.ofNat 64 off) ++ [.stdx x b scratch]

/-! ## The compiler -/

def instr : Limb.Instr → List Ppc.Instr
  | .mov d s => [.or (phys d) (phys s) (phys s)]
  | .movi d v => movImm (phys d) v
  | .lea d l off => .adr (phys d) l :: (if off = 0 then [] else addOff (phys d) off)
  | .ld d b off => ldOff (phys d) (phys b) off
  | .ldbe d b off => movImm scratch (BitVec.ofNat 64 off) ++ [.ldbrx (phys d) (phys b) scratch]
  | .st b off s => stOff (phys s) (phys b) off
  | .mulx hi lo b => [.mulld (phys lo) (phys 0) (phys b), .mulhdu (phys hi) (phys 0) (phys b)]
  | .add d s => [.addc (phys d) (phys d) (phys s)]
  | .adc d s => [.adde (phys d) (phys d) (phys s)]
  | .sub d s => [.subfc (phys d) (phys s) (phys d)]
  | .sbb d s => [.subfe (phys d) (phys s) (phys d)]
  | .mask d => [.subfe (phys d) (phys d) (phys d)]
  | .and d s => [.and (phys d) (phys d) (phys s)]
  | .or d s => [.or (phys d) (phys d) (phys s)]
  | .xor d s => [.xor (phys d) (phys d) (phys s)]
  | .shr d n => [.rldicl (phys d) (phys d) ((64 - n) % 64) n]
  | .shl d n => [.rldicr (phys d) (phys d) n (63 - n)]
  | .addi d n => addOff (phys d) n
  | .subi d n => movImm scratch (BitVec.ofNat 64 n) ++ [.subf (phys d) scratch (phys d)]
  | .clrc => []

def cond : Limb.Cond → List Ppc.Instr × Ppc.Cond
  | .eqz v => ([.cmpldi (phys v) 0], .eq)
  | .nez v => ([.cmpldi (phys v) 0], .ne)

def compiler : Compiler Limb.isa Ppc.isa := ⟨instr, cond⟩

/-- The simulation relation.  `f` is the machine state on entry: the link
register, CR1–CR7, the vector and VSX registers and every GPR other than the
IR registers and the scratch `r0` keep their values from `f`. -/
structure Rel (f : Ppc.State) (s : Limb.State) (t : Ppc.State) : Prop where
  regs : ∀ v, t.getG (phys v) = s.r v
  /-- `CA` is the IR carry, or its negation after a subtraction -/
  cf : ∀ c, s.cf = some c → t.ca = some (if s.sub then !c else c)
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  labels : t.labels = s.labels
  lr : t.lr = f.lr
  v : t.v = f.v
  vsr : t.vsr = f.vsr
  cr1to7 : t.cr1to7 = f.cr1to7
  frame : ∀ r, (∀ v, phys v ≠ r) → r ≠ scratch → t.getG r = f.getG r

/-! ## Lemmas about the relation -/

theorem getG_setG_phys (t : Ppc.State) (d v : Var) (x : BitVec 64) :
    (t.setG (phys d) x).getG (phys v) = if v = d then x else t.getG (phys v) := by
  rw [State.getG_setG]; simp only [phys_inj]

theorem getG_setG_scratch_phys (t : Ppc.State) (v : Var) (x : BitVec 64) :
    (t.setG scratch x).getG (phys v) = t.getG (phys v) :=
  State.getG_setG_ne _ _ _ _ (phys_ne_scratch v)

theorem Rel.setGca {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (d : Var) (x : BitVec 64)
    (cf : Option Bool) (sub : Bool) (ca : Option Bool)
    (hcf : ∀ c, cf = some c → ca = some (if sub then !c else c)) :
    Rel f { s.set d x with cf := cf, sub := sub } { t.setG (phys d) x with ca := ca } := by
  refine ⟨fun v => ?_, hcf, h.mem, h.rd, h.wr, h.labels, h.lr, h.v, h.vsr, h.cr1to7, fun r hr hs => ?_⟩
  · show (t.setG (phys d) x).getG (phys v) = _
    rw [getG_setG_phys]
    simp only [Limb.State.set, Function.update_apply]
    split_ifs <;> [rfl; exact h.regs v]
  · show (t.setG (phys d) x).getG r = _
    rw [State.getG_setG_ne _ _ _ _ (Ne.symm (hr d))]; exact h.frame r hr hs

/-- Writing an IR register, keeping the IR carry. -/
theorem Rel.set {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (d : Var) (x : BitVec 64) :
    Rel f (s.set d x) (t.setG (phys d) x) :=
  h.setGca d x s.cf s.sub t.ca h.cf

/-- Writing an IR register, forgetting the IR carry. -/
theorem Rel.setNone {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (d : Var) (x : BitVec 64) :
    Rel f { s.set d x with cf := none } (t.setG (phys d) x) :=
  h.setGca d x none s.sub t.ca (fun _ hc => by cases hc)

/-- A carrying instruction. -/
theorem Rel.setCA {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (d : Var) (x : BitVec 64)
    (c sub : Bool) (p : BitVec 64 × Bool) (hx : p.1 = x) (hc : p.2 = if sub then !c else c) :
    Rel f { s.set d x with cf := some c, sub := sub } (t.setGCA (phys d) p) := by
  subst hx
  exact h.setGca d p.1 (some c) sub (some p.2) (fun c' hc' => by cases hc'; rw [hc])

theorem Rel.setScratch {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (x : BitVec 64) :
    Rel f s (t.setG scratch x) := by
  refine ⟨fun v => ?_, h.cf, h.mem, h.rd, h.wr, h.labels, h.lr, h.v, h.vsr, h.cr1to7, fun r hr hs => ?_⟩
  · rw [getG_setG_scratch_phys]; exact h.regs v
  · rw [State.getG_setG_ne _ _ _ _ hs]; exact h.frame r hr hs

theorem Rel.mem' {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (m : Mem) :
    Rel f { s with mem := m } { t with mem := m } :=
  ⟨h.regs, h.cf, rfl, h.rd, h.wr, h.labels, h.lr, h.v, h.vsr, h.cr1to7, h.frame⟩

theorem Rel.forget {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) :
    Rel f { s with cf := none } t :=
  ⟨h.regs, fun _ hc => (by cases hc), h.mem, h.rd, h.wr, h.labels, h.lr, h.v, h.vsr, h.cr1to7, h.frame⟩

theorem Rel.cr0 {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (h : Rel f s t) (a b c : Option Bool) :
    Rel f s { t with lt := a, gt := b, eq := c } :=
  ⟨h.regs, h.cf, h.mem, h.rd, h.wr, h.labels, h.lr, h.v, h.vsr, h.cr1to7, h.frame⟩

/-! ## Arithmetic facts -/

theorem addCarry_res (a b : BitVec 64) (c : Bool) :
    (addCarry a b c).1 = a + b + (BitVec.ofBool c).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  cases c <;> simp [addCarry, BitVec.toNat_add, Nat.add_mod]

theorem addCarry_carry (a b : BitVec 64) (c : Bool) : (addCarry a b c).2 = carryOut a b c := rfl

theorem addCarry_sub_res (a b : BitVec 64) (c : Bool) :
    (addCarry (~~~b) a (!c)).1 = a - b - (BitVec.ofBool c).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  cases c <;> simp [addCarry, BitVec.toNat_sub, BitVec.toNat_not] <;> omega

theorem addCarry_sub_carry (a b : BitVec 64) (c : Bool) :
    (addCarry (~~~b) a (!c)).2 = !borrowOut a b c := by
  have hb : b.toNat < 18446744073709551616 := b.isLt
  have hn : (~~~b).toNat = 18446744073709551615 - b.toNat := BitVec.toNat_not
  rw [Bool.eq_iff_iff]
  cases c <;> simp only [addCarry, borrowOut, hn, Nat.ble_eq, Nat.blt_eq, Bool.not_true,
    Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.not_eq_true', Nat.reducePow, Bool.eq_false_iff,
    ne_eq] <;> omega

theorem addCarry_mask (x : BitVec 64) (c : Bool) :
    addCarry (~~~x) x (!c) = (if c then BitVec.allOnes 64 else 0, !c) := by
  have hx : x.toNat < 18446744073709551616 := x.isLt
  have hn : (~~~x).toNat = 18446744073709551615 - x.toNat := BitVec.toNat_not
  cases c
  · simp only [addCarry, hn, Bool.not_false, Bool.toNat_true, Bool.false_eq_true, ite_false]
    rw [show 18446744073709551615 - x.toNat + x.toNat + 1 = 2 ^ 64 by omega]
    simp
  · simp only [addCarry, hn, Bool.not_true, Bool.toNat_false, ite_true]
    rw [show 18446744073709551615 - x.toNat + x.toNat + 0 = 2 ^ 64 - 1 by omega]
    simp only [Prod.mk.injEq]
    constructor
    · apply BitVec.eq_of_toNat_eq; simp
    · decide

theorem subf_eq (a b : BitVec 64) : ~~~a + b + 1 = b - a := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, show (1#64 : BitVec 64) = 1 from rfl]; ac_rfl

theorem shl_eq (x : BitVec 64) (n : Nat) (hn : n < 64) :
    rotl64 x n &&& maskTo (63 - n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [rotl64, maskTo, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt hn, show 63 - (63 - n) = n by omega, hi, decide_true,
    Bool.true_and]
  by_cases h : i < n
  · simp [h]
  · simp [h, hi]; intro; omega

theorem shr_eq (x : BitVec 64) (n : Nat) (hn : n < 64) :
    rotl64 x ((64 - n) % 64) &&& maskFrom n = x >>> n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [rotl64, maskFrom, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Nat.mod_mod, hi, decide_true, Bool.true_and]
  by_cases h0 : n = 0
  · subst h0; simp; exact fun _ => hi
  · rw [Nat.mod_eq_of_lt (show 64 - n < 64 by omega)]
    by_cases h : i < 64 - n
    · simp only [h, ite_true]
      rw [show 64 - (64 - n) + i = n + i by omega]; simp [show n + i < 64 by omega]
    · simp only [h, ite_false]
      rw [BitVec.getLsbD_of_ge x (n + i) (by omega)]; simp [show ¬ n + i < 64 by omega]


theorem movImm_long (v : BitVec 64) :
    (rotl64 ((0 + BitVec.ofInt 64 0 ||| BitVec.ofNat 64 (chunk v 3 % 2 ^ 16 * 2 ^ 16)) |||
      BitVec.ofNat 64 (chunk v 2 % 2 ^ 16)) 32 &&& maskTo 31 |||
      BitVec.ofNat 64 (chunk v 1 % 2 ^ 16 * 2 ^ 16) ||| BitVec.ofNat 64 (chunk v 0 % 2 ^ 16)) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [chunk, rotl64, maskTo, Nat.mod_mod, BitVec.ofInt_ofNat, BitVec.add_zero, BitVec.zero_or,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  simp only [BitVec.testBit_toNat]
  interval_cases i <;> simp


theorem movImm_short (v : BitVec 64) (_h : v.toNat < 32768) : 0 + BitVec.ofInt 64 (v.toNat : Int) = v := by
  rw [zero_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Executing short sequences -/

theorem execBlock_append_some {l₁ l₂ : List Ppc.Instr} {t t₁ t₂ : Ppc.State}
    (h₁ : execBlock Ppc.isa l₁ t = some (t₁, [])) (h₂ : execBlock Ppc.isa l₂ t₁ = some (t₂, [])) :
    execBlock Ppc.isa (l₁ ++ l₂) t = some (t₂, []) := by
  rw [execBlock_append, h₁]; simp [h₂]

theorem GRegs.set_set (g : GRegs) (r : GReg) (x y : BitVec 64) : (g.set r x).set r y = g.set r y := by
  cases r <;> rfl

theorem setG_setG (t : Ppc.State) (r : GReg) (x y : BitVec 64) : (t.setG r x).setG r y = t.setG r y := by
  simp only [State.setG, GRegs.set_set]

theorem exec1 (i : Ppc.Instr) (t t' : Ppc.State) (h : CC.Ppc.exec i t = some t') (ha : CC.Ppc.addrs i t = []) :
    execBlock Ppc.isa [i] t = some (t', []) := by
  simp [execBlock, Ppc.isa, h, ha]

theorem movImm_exec (t : Ppc.State) (r : GReg) (v : BitVec 64) :
    execBlock Ppc.isa (movImm r v) t = some (t.setG r v, []) := by
  unfold movImm
  split_ifs with h
  · apply exec1 _ _ _ _ rfl
    simp only [CC.Ppc.exec, State.raOr0, movImm_short v h]
  · simp only [execBlock, Ppc.isa, CC.Ppc.exec, CC.Ppc.addrs, State.raOr0, State.getG_setG_same,
      setG_setG, Option.map_some, List.map_nil, List.append_nil, show (32 < 64 ∧ 31 < 64) = True from
      propext ⟨fun _ => trivial, fun _ => ⟨by decide, by decide⟩⟩, ite_true]
    rw [movImm_long]

/-! ## Simulation -/

/-- A single instruction simulating an IR step (the target state `t'` is given by `hR`). -/
theorem sim1 {f t : Ppc.State} {s' : Limb.State} (i : Ppc.Instr) {t' : Ppc.State} (hR : Rel f s' t')
    (h : CC.Ppc.exec i t = some t') : ∃ q, execBlock Ppc.isa [i] t = some q ∧ Rel f s' q.1 :=
  ⟨(t', (CC.Ppc.addrs i t).map Leak.addr), by simp [execBlock, Ppc.isa, h], hR⟩

/-- An instruction after materializing `off` in the scratch register. -/
theorem simS {f t : Ppc.State} {s' : Limb.State} (off : Nat) (i : Ppc.Instr) {t' : Ppc.State}
    (hR : Rel f s' t') (h : CC.Ppc.exec i (t.setG scratch (BitVec.ofNat 64 off)) = some t') :
    ∃ q, execBlock Ppc.isa (movImm scratch (BitVec.ofNat 64 off) ++ [i]) t = some q ∧ Rel f s' q.1 := by
  refine ⟨(t', (CC.Ppc.addrs i (t.setG scratch (BitVec.ofNat 64 off))).map Leak.addr), ?_, hR⟩
  rw [execBlock_append, movImm_exec]; simp [execBlock, Ppc.isa, h]

theorem sim_app {f t : Ppc.State} {s₁ s₂ : Limb.State} {l₁ l₂ : List Ppc.Instr}
    (h₁ : ∃ q, execBlock Ppc.isa l₁ t = some q ∧ Rel f s₁ q.1)
    (h₂ : ∀ t₁, Rel f s₁ t₁ → ∃ q, execBlock Ppc.isa l₂ t₁ = some q ∧ Rel f s₂ q.1) :
    ∃ q, execBlock Ppc.isa (l₁ ++ l₂) t = some q ∧ Rel f s₂ q.1 := by
  obtain ⟨q₁, e₁, r₁⟩ := h₁
  obtain ⟨q₂, e₂, r₂⟩ := h₂ q₁.1 r₁
  exact ⟨(q₂.1, q₁.2 ++ q₂.2), by rw [execBlock_append, e₁]; simp [e₂], r₂⟩

theorem ea_scratch (t : Ppc.State) (b : Var) (x : BitVec 64) :
    (t.setG scratch x).ea (phys b) scratch = t.getG (phys b) + x := by
  simp only [State.ea, raOr0_phys, getG_setG_scratch_phys, State.getG_setG_same]

theorem ldOff_exec {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (hr : Rel f s t) (d b : Var) (off : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.r b + BitVec.ofNat 64 off) 8) :
    ∃ q, execBlock Ppc.isa (ldOff (phys d) (phys b) off) t = some q ∧
      Rel f (s.set d (s.mem.readW (s.r b + BitVec.ofNat 64 off) 64)) q.1 := by
  unfold ldOff
  split_ifs
  · refine sim1 _ (hr.set d _) ?_
    simp only [CC.Ppc.exec, State.load64, raOr0_phys, hr.regs, hr.rd, hr.wr, hp, ite_true,
      Option.map_some, hr.mem]
  · refine simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _) ?_
    simp only [CC.Ppc.exec, State.load64, ea_scratch, hr.regs, State.setG_rd, State.setG_wr,
      State.setG_mem, hr.rd, hr.wr, hp, ite_true, Option.map_some, hr.mem]

theorem stOff_exec {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (hr : Rel f s t) (x b : Var) (off : Nat)
    (hp : InRegions s.wr (s.r b + BitVec.ofNat 64 off) 8) :
    ∃ q, execBlock Ppc.isa (stOff (phys x) (phys b) off) t = some q ∧
      Rel f { s with mem := s.mem.writeW (s.r b + BitVec.ofNat 64 off) (s.r x) } q.1 := by
  unfold stOff
  split_ifs
  · refine sim1 _ (hr.mem' _) ?_
    simp only [CC.Ppc.exec, State.store64, raOr0_phys, hr.regs, hr.wr, hp, ite_true, hr.mem]
  · refine simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).mem' _) ?_
    simp only [CC.Ppc.exec, State.store64, ea_scratch, getG_setG_scratch_phys, hr.regs,
      State.setG_wr, State.setG_mem, hr.wr, hp, ite_true, hr.mem]

theorem addOff_exec {f : Ppc.State} {s : Limb.State} {t : Ppc.State} (hr : Rel f s t) (d : Var) (off : Nat) :
    ∃ q, execBlock Ppc.isa (addOff (phys d) off) t = some q ∧
      Rel f (s.set d (s.r d + BitVec.ofNat 64 off)) q.1 := by
  unfold addOff
  split_ifs
  · exact sim1 _ (hr.set d _) (by simp only [CC.Ppc.exec, raOr0_phys, hr.regs, BitVec.ofInt_natCast])
  · exact simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _)
      (by simp only [CC.Ppc.exec, getG_setG_scratch_phys, State.getG_setG_same, hr.regs])

theorem set_set (s : Limb.State) (d : Var) (x y : BitVec 64) : (s.set d x).set d y = s.set d y := by
  simp only [Limb.State.set, Function.update_idem]

theorem set_r_self (s : Limb.State) (d : Var) (x : BitVec 64) : (s.set d x).r d = x := by
  simp only [Limb.State.set, Function.update_self]

theorem revBytes64_eq (x : BitVec 64) : revBytes64 x = bswap64 x := rfl

theorem sim_instr (f : Ppc.State) (i : Limb.Instr) (s s' : Limb.State) (t : Ppc.State) (hr : Rel f s t)
    (he : Limb.isa.exec i s = some s') :
    ∃ q, execBlock Ppc.isa (compiler.instr i) t = some q ∧ Rel f s' q.1 := by
  cases i with
  | mov d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.set d _) (by simp only [CC.Ppc.exec, hr.regs, BitVec.or_self])
  | movi d v =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact ⟨_, movImm_exec _ _ _, hr.set d v⟩
  | lea d l off =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    have hR := (hr.setScratch t.lr).set d (s.labels l)
    have h1 := sim1 (t := t) (.adr (phys d) l) hR (by
      -- `phys d` is neither `r0` nor `r1`, so `adr` does not fault
      have h0 := phys_ne_scratch d; have h1 := phys_ne_r1 d
      simp only [CC.Ppc.exec, hr.labels])
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
      refine simS off _ ((hr.setScratch (BitVec.ofNat 64 off)).set d _) ?_
      simp only [CC.Ppc.exec, State.load64, ea_scratch, hr.regs, State.setG_rd, State.setG_wr,
        State.setG_mem, hr.rd, hr.wr, hp, ite_true, Option.map_some, hr.mem, revBytes64_eq]
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
          (by simp only [CC.Ppc.exec, hr.regs])) (fun t₁ hr₁ => ?_)
      have e0 := hr₁.regs 0
      have eb := hr₁.regs b
      simp only [Limb.State.set, Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm hb)] at e0 eb
      exact sim1 _ (hr₁.set hi _) (by simp only [CC.Ppc.exec, e0, eb])
  | add d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setCA d _ _ false (addCarry (s.r d) (s.r x) false) (by rw [addCarry_res]; simp)
      (by rw [addCarry_carry]; rfl)) (by simp only [CC.Ppc.exec, hr.regs])
  | sub d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setCA d _ _ true (addCarry (~~~(s.r x)) (s.r d) (!false))
      (by rw [addCarry_sub_res]; simp) (by rw [addCarry_sub_carry]; rfl))
      (by simp only [CC.Ppc.exec, hr.regs, Bool.not_false])
  | adc d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.ca = some c := by simpa [hsub] using hr.cf c hcf
      exact sim1 _ (hr.setCA d _ _ false (addCarry (s.r d) (s.r x) c) (by rw [addCarry_res])
        (by rw [addCarry_carry]; rfl)) (by simp only [CC.Ppc.exec, hr.regs, htc, Option.map_some])
    · cases he
  | sbb d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.ca = some (!c) := by simpa [hsub] using hr.cf c hcf
      exact sim1 _ (hr.setCA d _ _ true (addCarry (~~~(s.r x)) (s.r d) (!c)) (by rw [addCarry_sub_res])
        (by rw [addCarry_sub_carry]; rfl)) (by simp only [CC.Ppc.exec, hr.regs, htc, Option.map_some])
    · cases he
  | mask d =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc : t.ca = some (!c) := by simpa [hsub] using hr.cf c hcf
      have hR := hr.setCA d (if c then BitVec.allOnes 64 else 0) c true
        (addCarry (~~~(s.r d)) (s.r d) (!c)) (by rw [addCarry_mask]) (by rw [addCarry_mask]; rfl)
      have e : ({ s.set d (if c then BitVec.allOnes 64 else 0) with cf := some c, sub := true } : Limb.State) =
          s.set d (if c then BitVec.allOnes 64 else 0) := by
        cases s; simp only [Limb.State.set] at hcf hsub ⊢; subst hcf hsub; rfl
      rw [e] at hR
      exact sim1 _ hR (by simp only [CC.Ppc.exec, hr.regs, htc, Option.map_some])
    · cases he
  | and d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Ppc.exec, hr.regs])
  | or d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Ppc.exec, hr.regs])
  | xor d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact sim1 _ (hr.setNone d _) (by simp only [CC.Ppc.exec, hr.regs])
  | shr d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      exact sim1 _ (hr.setNone d _) (by
        simp only [CC.Ppc.exec, hr.regs, shr_eq _ _ hn, Nat.mod_lt _ (show 64 > 0 by decide), hn,
          and_self, ite_true])
    · cases he
  | shl d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      exact sim1 _ (hr.setNone d _) (by
        simp only [CC.Ppc.exec, hr.regs, shl_eq _ _ hn, hn, show 63 - n < 64 by omega, and_self, ite_true])
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
      exact simS n _ ((hr.setScratch (BitVec.ofNat 64 n)).setNone d _)
        (by simp only [CC.Ppc.exec, getG_setG_scratch_phys, State.getG_setG_same, hr.regs, subf_eq])
    · cases he
  | clrc =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    exact ⟨(t, []), rfl, hr.forget⟩

theorem sim_cond (f : Ppc.State) (c : Limb.Cond) (s : Limb.State) (t : Ppc.State) (b : Bool) (hr : Rel f s t)
    (he : Limb.isa.eval c s = some b) :
    ∃ q, execBlock Ppc.isa (compiler.cond c).1 t = some q ∧ Rel f s q.1 ∧
      Ppc.isa.eval (compiler.cond c).2 q.1 = some b := by
  simp only [Limb.eval] at he
  split at he
  · cases he
  · cases c with
    | eqz v =>
      simp only [Option.some.injEq] at he; subst he
      refine ⟨_, exec1 _ _ _ rfl rfl, hr.cr0 _ _ _, ?_⟩
      simp only [compiler, cond, Ppc.isa, evalCond, hr.regs v]; rfl
    | nez v =>
      simp only [Option.some.injEq] at he; subst he
      refine ⟨_, exec1 _ _ _ rfl rfl, hr.cr0 _ _ _, ?_⟩
      simp only [compiler, cond, Ppc.isa, evalCond, hr.regs v, Option.map_some]; rfl

/-- **The IR-to-ppc64le compiler is correct**: `f` is the machine state on entry,
whose link register, CR1–CR7, vector/VSX registers and non-IR GPRs (other than
the scratch `r0`) are preserved. -/
theorem sim (f : Ppc.State) : compiler.Sim (Rel f) :=
  ⟨fun i s s' t hr he => sim_instr f i s s' t hr he, fun c s t b hr he => sim_cond f c s t b hr he⟩

end CC.Limb.Ppc
