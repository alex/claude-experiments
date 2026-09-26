import ClaudeCrypto.Limb.Basic
import ClaudeCrypto.Framework.Compile
import ClaudeCrypto.X86.Taint

/-!
# Compiling the limb IR to x86-64

Each IR register is a fixed x86 register (`rsp` is never used; IR register 0,
the `mulx` multiplicand, is `rdx`).  Each IR instruction becomes one x86
instruction (`clrc` none), and a branch on `r = 0` becomes `test r, r` followed
by `je`/`jne`.  `sim` proves the simulation obligations of
`Framework/Compile.lean`, so every proven IR program yields proven x86 code.
-/

namespace CC.Limb.X86

open CC.X86

/-- The x86 register holding each IR register. -/
def phys : Var → Reg
  | 0 => .rdx | 1 => .rax | 2 => .rcx | 3 => .rbx | 4 => .rsi | 5 => .rdi | 6 => .rbp
  | 7 => .r8 | 8 => .r9 | 9 => .r10 | 10 => .r11 | 11 => .r12 | 12 => .r13 | 13 => .r14 | 14 => .r15

theorem phys_inj (a b : Var) : phys a = phys b ↔ a = b := by
  constructor
  · revert a b; decide
  · rintro rfl; rfl

theorem phys_ne_rsp (a : Var) : phys a ≠ .rsp := by revert a; decide

def mo (b : Var) (off : Nat) : MemOp := { base := phys b, disp := (off : Int) }

def instr : Limb.Instr → List X86.Instr
  | .mov d s => [.mov .q (phys d) (.reg (phys s))]
  | .movi d v => [.movabs (phys d) v]
  | .lea d l off => [.lea .q (phys d) { rip := some l, disp := (off : Int) }]
  | .ld d b off => [.mov .q (phys d) (.mem (mo b off))]
  | .ldbe d b off => [.movbe .q (phys d) (mo b off)]
  | .st b off s => [.store .q (mo b off) (phys s)]
  | .mulx hi lo b => [.mulx (phys hi) (phys lo) (phys b)]
  | .add d s => [.alu .add .q (phys d) (.reg (phys s))]
  | .adc d s => [.alu .adc .q (phys d) (.reg (phys s))]
  | .sub d s => [.alu .sub .q (phys d) (.reg (phys s))]
  | .sbb d s => [.alu .sbb .q (phys d) (.reg (phys s))]
  | .mask d => [.alu .sbb .q (phys d) (.reg (phys d))]
  | .and d s => [.alu .and .q (phys d) (.reg (phys s))]
  | .or d s => [.alu .or .q (phys d) (.reg (phys s))]
  | .xor d s => [.alu .xor .q (phys d) (.reg (phys s))]
  | .shr d n => [.shift .shr .q (phys d) n]
  | .shl d n => [.shift .shl .q (phys d) n]
  | .addi d n => [.alu .add .q (phys d) (.imm (BitVec.ofNat 32 n))]
  | .subi d n => [.alu .sub .q (phys d) (.imm (BitVec.ofNat 32 n))]
  | .clrc => []

def cond : Limb.Cond → List X86.Instr × X86.Cond
  | .eqz v => ([.alu .test .q (phys v) (.reg (phys v))], .e)
  | .nez v => ([.alu .test .q (phys v) (.reg (phys v))], .ne)

def compiler : Compiler Limb.isa X86.isa := ⟨instr, cond⟩

/-- The simulation relation; `sp` is the (untouched) stack pointer. -/
structure Rel (sp : Addr) (s : Limb.State) (t : X86.State) : Prop where
  regs : ∀ v, t.gpr.get (phys v) = s.r v
  cf : ∀ c, s.cf = some c → t.cf = some c
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  labels : t.labels = s.labels
  rsp : t.gpr.rsp = sp

theorem Rel.set {sp : Addr} {s : Limb.State} {t : X86.State} (h : Rel sp s t) (d : Var) (v : BitVec 64)
    (cf : Option Bool) (sub : Bool) (tcf : Option Bool) (hcf : ∀ c, cf = some c → tcf = some c) :
    Rel sp { s.set d v with cf := cf, sub := sub }
      { t.setReg (phys d) v with cf := tcf, of := t.of, zf := t.zf, sf := t.sf } := by
  refine ⟨fun v' => ?_, hcf, h.mem, h.rd, h.wr, h.labels, ?_⟩
  · simp only [State.setReg, Regs.get_set, Limb.State.set, Function.update, phys_inj]
    split_ifs with he
    · subst he; rfl
    · exact h.regs v'
  · show (t.gpr.set (phys d) v).get .rsp = sp
    rw [Regs.get_set, if_neg (Ne.symm (phys_ne_rsp d))]; exact h.rsp

theorem get_set_phys (g : Regs) (d v : Var) (x : BitVec 64) :
    (g.set (phys d) x).get (phys v) = if v = d then x else g.get (phys v) := by
  rw [Regs.get_set]; simp only [phys_inj]

theorem get_set_rsp (g : Regs) (d : Var) (x : BitVec 64) : (g.set (phys d) x).get .rsp = g.get .rsp := by
  rw [Regs.get_set, if_neg (Ne.symm (phys_ne_rsp d))]

theorem update_apply (f : Var → BitVec 64) (d v : Var) (x : BitVec 64) :
    Function.update f d x v = if v = d then x else f v := by
  by_cases h : v = d
  · subst h; simp
  · simp [h]

theorem ea_mo (t : X86.State) (b : Var) (off : Nat) :
    t.ea (mo b off) = t.gpr.get (phys b) + BitVec.ofNat 64 off := by
  simp only [State.ea, mo, State.getReg, BitVec.ofInt_natCast]

theorem signExtend_ofNat (n : Nat) (h : n < 2 ^ 31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    simp [BitVec.msb_eq_decide, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Registers after writing `x` to IR register `d`. -/
theorem regs_set {sp : Addr} {s : Limb.State} {t : X86.State} (h : Rel sp s t) (d : Var) (x : BitVec 64) :
    ∀ v, (t.gpr.set (phys d) x).get (phys v) = Function.update s.r d x v := by
  intro v; rw [get_set_phys, update_apply]; split_ifs <;> [rfl; exact h.regs v]

set_option hygiene false in
macro "x86_step" : tactic => `(tactic| (
  simp only [compiler, instr, execBlock, X86.isa, X86.exec, Instr.sz, execW, execAlu, execShift, readSrc,
    State.readW, State.writeW, State.setReg, State.getReg, arithFlags, setFlags, BitVec.setWidth_eq,
    Option.map_some, Option.bind_some, hr.regs, State.loadW, State.storeW,
    hr.rd, hr.wr, hr.mem]))

set_option hygiene false in
macro "rel_fin" : tactic => `(tactic| (
  refine ⟨regs_set hr _ _, ?_, rfl, rfl, rfl, by first | exact hr.labels | rfl, ?_⟩
  · intro c hc
    first
      | exact hr.cf c hc
      | (simp only [Limb.State.set, reduceCtorEq] at hc; done)
      | (simp only [Limb.State.set, Option.some.injEq] at hc ⊢; subst hc; simp [carryOut, borrowOut])
  · show (t.gpr.set _ _).get .rsp = sp; rw [get_set_rsp]; exact hr.rsp))

theorem sim_instr (sp : Addr) (i : Limb.Instr) (s s' : Limb.State) (t : X86.State) (hr : Rel sp s t)
    (he : Limb.isa.exec i s = some s') :
    ∃ q, execBlock X86.isa (compiler.instr i) t = some q ∧ Rel sp s' q.1 := by
  cases i with
  | mov d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | movi d v =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | add d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | sub d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | lea d l off =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; simp only [State.ea, BitVec.ofInt_natCast, hr.labels]; refine ⟨_, rfl, ?_⟩; rel_fin
  | ld d b off =>
    simp only [Limb.isa, Limb.exec, Limb.State.load] at he
    split at he
    · rename_i hp
      simp only [Option.map_some, Option.some.injEq] at he; subst he
      x86_step; simp only [ea_mo, hr.regs, Nat.reduceDiv, hp, ite_true, Option.map_some]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | ldbe d b off =>
    simp only [Limb.isa, Limb.exec, Limb.State.load] at he
    split at he
    · rename_i hp
      simp only [Option.map_some, Option.some.injEq] at he; subst he
      x86_step; simp only [ea_mo, hr.regs, Nat.reduceDiv, hp, ite_true, Option.map_some]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | st b off x =>
    simp only [Limb.isa, Limb.exec, Limb.State.store] at he
    split at he
    · rename_i hp
      simp only [Option.some.injEq] at he; subst he
      x86_step; simp only [ea_mo, hr.regs, Nat.reduceDiv, hp, ite_true, Option.map_some]
      refine ⟨_, rfl, ⟨hr.regs, hr.cf, rfl, rfl, rfl, hr.labels, hr.rsp⟩⟩
    · cases he
  | mulx hi lo b =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · cases he
    · rename_i hc
      simp only [Option.some.injEq] at he; subst he
      x86_step
      refine ⟨_, rfl, ⟨fun v => ?_, hr.cf, rfl, rfl, rfl, hr.labels, ?_⟩⟩
      · have h0 : t.gpr.get .rdx = s.r 0 := hr.regs 0
        simp only [get_set_phys, Limb.State.set, update_apply, h0, hr.regs]
        try (split_ifs <;> rfl)
      · show ((t.gpr.set _ _).set _ _).get .rsp = sp; rw [get_set_rsp, get_set_rsp]; exact hr.rsp
  | adc d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc := hr.cf c hcf
      x86_step; simp only [htc, Option.map_some]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | sbb d x =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc := hr.cf c hcf
      x86_step; simp only [htc, Option.map_some]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | mask d =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i c hcf hsub
      simp only [Option.some.injEq] at he; subst he
      have htc := hr.cf c hcf
      x86_step; simp only [htc, Option.map_some]
      refine ⟨_, rfl, ⟨fun v => ?_, fun c' hc' => ?_, rfl, rfl, rfl, hr.labels, ?_⟩⟩
      · rw [regs_set hr d]
        congr 1
        cases c <;> simp
      · simp only [Limb.State.set] at hc'
        rw [hcf] at hc'; cases hc'
        cases c
        · simp only [BitVec.ofBool_false, Bool.toNat_false, Nat.add_zero, Option.some.injEq]
          exact Bool.eq_false_iff.mpr (by simp [Nat.blt_eq])
        · simp [Nat.blt_eq]
      · show (t.gpr.set _ _).get .rsp = sp; rw [get_set_rsp]; exact hr.rsp
    · cases he
  | and d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | or d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | xor d x =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    x86_step; refine ⟨_, rfl, ?_⟩; rel_fin
  | shr d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      by_cases hn0 : n = 0
      · subst hn0
        x86_step
        refine ⟨_, rfl, ⟨fun v => ?_, fun c hc => by simp [Limb.State.set] at hc, hr.mem, hr.rd, hr.wr, hr.labels, hr.rsp⟩⟩
        simp only [Limb.State.set, update_apply, BitVec.ushiftRight_zero]
        split_ifs with h <;> [subst h; skip] <;> exact hr.regs _
      · x86_step; simp only [Nat.mod_eq_of_lt hn, hn0, ite_false]
        refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | shl d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      by_cases hn0 : n = 0
      · subst hn0
        x86_step
        refine ⟨_, rfl, ⟨fun v => ?_, fun c hc => by simp [Limb.State.set] at hc, hr.mem, hr.rd, hr.wr, hr.labels, hr.rsp⟩⟩
        simp only [Limb.State.set, update_apply, BitVec.shiftLeft_zero]
        split_ifs with h <;> [subst h; skip] <;> exact hr.regs _
      · x86_step; simp only [Nat.mod_eq_of_lt hn, hn0, ite_false]
        refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | addi d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      x86_step; simp only [signExtend_ofNat n hn]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | subi d n =>
    simp only [Limb.isa, Limb.exec] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he; subst he
      x86_step; simp only [signExtend_ofNat n hn]
      refine ⟨_, rfl, ?_⟩; rel_fin
    · cases he
  | clrc =>
    simp only [Limb.isa, Limb.exec, Option.some.injEq] at he; subst he
    refine ⟨(t, []), rfl, ⟨hr.regs, fun c hc => (by simp at hc), hr.mem, hr.rd, hr.wr, hr.labels, hr.rsp⟩⟩

theorem sim_cond (sp : Addr) (c : Limb.Cond) (s : Limb.State) (t : X86.State) (b : Bool) (hr : Rel sp s t)
    (he : Limb.isa.eval c s = some b) :
    ∃ q, execBlock X86.isa (compiler.cond c).1 t = some q ∧ Rel sp s q.1 ∧
      X86.isa.eval (compiler.cond c).2 q.1 = some b := by
  simp only [Limb.isa, Limb.eval] at he
  split at he
  · cases he
  · rename_i hcf
    cases c with
    | eqz v =>
      simp only [Option.some.injEq] at he; subst he
      simp only [compiler, cond, execBlock, X86.isa, X86.exec, Instr.sz, execW, execAlu, readSrc,
        State.readW, arithFlags, setFlags, BitVec.setWidth_eq, Option.map_some, Option.bind_some, hr.regs,
        BitVec.and_self]
      exact ⟨_, rfl, ⟨hr.regs, fun c hc => (by rw [hcf] at hc; cases hc), hr.mem, hr.rd, hr.wr, hr.labels, hr.rsp⟩,
        rfl⟩
    | nez v =>
      simp only [Option.some.injEq] at he; subst he
      simp only [compiler, cond, execBlock, X86.isa, X86.exec, Instr.sz, execW, execAlu, readSrc,
        State.readW, arithFlags, setFlags, BitVec.setWidth_eq, Option.map_some, Option.bind_some, hr.regs,
        BitVec.and_self]
      exact ⟨_, rfl, ⟨hr.regs, fun c hc => (by rw [hcf] at hc; cases hc), hr.mem, hr.rd, hr.wr, hr.labels, hr.rsp⟩,
        by simp [evalCond, bne]⟩

/-- **The IR-to-x86 compiler is correct.** -/
theorem sim (sp : Addr) : compiler.Sim (Rel sp) :=
  ⟨fun i s s' t hr he => sim_instr sp i s s' t hr he, fun c s t b hr he => sim_cond sp c s t b hr he⟩

end CC.Limb.X86
