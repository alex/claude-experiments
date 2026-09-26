import ClaudeCrypto.X86.Basic
import ClaudeCrypto.Framework.Taint

/-!
# Taint domain for x86-64

Tracks, for each general-purpose register and for the flags (as a group),
whether the value is *public*.  Memory contents are always treated as secret
(every load produces a secret value), vector registers are not tracked (they
never feed an address or a branch), and every address computation must only
use public registers.
-/

namespace CC.X86

/-- Abstract state: a bitmask of public registers (bit `r.idx`) and whether
the flags are public.  (A bitmask keeps kernel evaluation of the analysis fast.) -/
structure TState where
  mask : Nat
  flags : Bool

def Reg.idx : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

theorem Reg.idx_lt (r : Reg) : r.idx < 16 := by cases r <;> decide

theorem Reg.idx_inj (r r' : Reg) : r.idx = r'.idx ↔ r = r' := by
  cases r <;> cases r' <;> decide

def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

namespace TState

def pub (t : TState) (r : Reg) : Bool := t.mask.testBit r.idx

def setPub (t : TState) (r : Reg) (b : Bool) : TState :=
  { t with mask := if b then t.mask ||| (1 <<< r.idx) else t.mask &&& (65535 ^^^ (1 <<< r.idx)) }

def memPub (t : TState) (m : MemOp) : Bool :=
  match m.rip with
  | some _ => true
  | none => t.pub m.base && (match m.index with | none => true | some i => t.pub i)

/-- Taint of a source operand; `none` if it is a memory operand with a secret address. -/
def srcPub (t : TState) : Src → Option Bool
  | .reg r => some (t.pub r)
  | .imm _ => some true
  | .mem m => if t.memPub m then some false else none

def step (i : Instr) (t : TState) : Option TState :=
  match i with
  | .mov _ dst src => (t.srcPub src).map (t.setPub dst)
  | .store _ m _ => if t.memPub m then some t else none
  | .alu op _ dst src => (t.srcPub src).map fun b =>
    let p := b && t.pub dst && (match op with | .adc | .sbb => t.flags | _ => true)
    match op with
    | .cmp | .test => { t with flags := p }
    | _ => ({ t with flags := p }).setPub dst p
  | .lea _ dst m => some (t.setPub dst (t.memPub m))
  | .rorx _ dst src _ => some (t.setPub dst (t.pub src))
  | .andn _ dst s1 s2 => (t.srcPub s2).map fun b =>
    let p := b && t.pub s1
    ({ t with flags := p }).setPub dst p
  | .shift _ _ dst _ =>
    let p := t.pub dst
    some (({ t with flags := p && t.flags }).setPub dst p)
  | .not _ dst => some (t.setPub dst (t.pub dst))
  | .movbe _ dst m => if t.memPub m then some (t.setPub dst false) else none
  | .bswap _ dst => some (t.setPub dst (t.pub dst))
  | .push _ => if t.pub .rsp then some t else none
  | .pop r => if t.pub .rsp then some ((t.setPub .rsp true).setPub r false) else none
  | .inc _ dst | .dec _ dst =>
    let p := t.pub dst
    some (({ t with flags := p && t.flags }).setPub dst p)
  -- SIMD: vector registers are not tracked (always secret); only addresses matter
  | .vload128 _ m | .vload256 _ m | .vstore256 m _ | .vinserti128hi _ _ m | .vbroadcasti128 _ m
  | .vpaddd _ _ (.mem m) | .movdquLd _ m | .movdquSt m _ => if t.memPub m then some t else none
  | .vpaddd _ _ (.reg _) | .vpshufb .. | .vpxor .. | .vpalignr .. | .vpsrld .. | .vpslld ..
  | .vpsrlq .. | .vpshufd .. | .vzeroupper
  | .movdqa .. | .paddd .. | .pshufb .. | .pshufd .. | .palignr .. | .punpcklqdq .. | .punpckhqdq ..
  | .sha256rnds2 .. | .sha256msg1 .. | .sha256msg2 .. => some t
  | .mulx hi lo src =>
    let p := t.pub .rdx && t.pub src
    some ((t.setPub lo p).setPub hi p)
  | .movabs dst _ => some (t.setPub dst true)

def condOk (_ : Cond) (t : TState) : Bool := t.flags

def join (a b : TState) : TState := ⟨a.mask &&& b.mask, a.flags && b.flags⟩

def le (a b : TState) : Bool := allRegs.all (fun r => !b.pub r || a.pub r) && (!b.flags || a.flags)

theorem join_pub (a b : TState) (r : Reg) : (a.join b).pub r = (a.pub r && b.pub r) := by
  simp [join, pub, Nat.testBit_and]

/-- `s₁` and `s₂` agree on all public registers and (if public) the flags. -/
def Agree (t : TState) (s₁ s₂ : State) : Prop :=
  (∀ r, t.pub r = true → s₁.gpr.get r = s₂.gpr.get r) ∧
  (t.flags = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of) ∧
  s₁.labels = s₂.labels

/-! ### Lemmas -/

theorem _root_.CC.X86.Regs.get_set (g : Regs) (r r' : Reg) (v : BitVec 64) :
    (g.set r v).get r' = if r' = r then v else g.get r' := by
  cases r <;> cases r' <;> rfl

theorem testBit_65535 (r : Reg) : (65535 : Nat).testBit r.idx = true := by cases r <;> decide

theorem setPub_pub (t : TState) (r r' : Reg) (b : Bool) :
    (t.setPub r b).pub r' = if r' = r then b else t.pub r' := by
  have h1 := Reg.idx_lt r; have h2 := Reg.idx_lt r'
  have hi := Reg.idx_inj r' r
  unfold setPub pub
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_and, Nat.testBit_xor, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    by_cases h : r' = r
    · subst h; simp [testBit_65535]
    · have : r.idx ≠ r'.idx := fun e => h (hi.mp e.symm)
      simp [h, this, testBit_65535]
  · simp only [↓reduceIte, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : r' = r
    · subst h; simp
    · have : r.idx ≠ r'.idx := fun e => h (hi.mp e.symm)
      simp [h, this]

theorem Agree.ea {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (m : MemOp)
    (hm : t.memPub m = true) : s₁.ea m = s₂.ea m := by
  unfold memPub at hm
  unfold State.ea State.getReg
  cases hr : m.rip with
  | some l => simp only [h.2.2]
  | none =>
    simp only [hr, Bool.and_eq_true] at hm
    simp only
    cases hi : m.index with
    | none => simp only; rw [h.1 _ hm.1]
    | some i => simp only [hi] at hm ⊢; rw [h.1 _ hm.1, h.1 _ hm.2]

theorem Agree.readW {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (w : Nat) (r : Reg)
    (hr : t.pub r = true) : s₁.readW w r = s₂.readW w r := by
  simp only [State.readW]; rw [h.1 r hr]

theorem Agree.writeW {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) {w : Nat} (r : Reg) (b : Bool)
    (v₁ v₂ : BitVec w) (hv : b = true → v₁ = v₂) :
    (t.setPub r b).Agree (s₁.writeW r v₁) (s₂.writeW r v₂) := by
  refine ⟨fun r' hr' => ?_, fun hf => h.2.1 hf, h.2.2⟩
  simp only [State.writeW, State.setReg, Regs.get_set]
  rw [setPub_pub] at hr'
  split_ifs at hr' ⊢ with he
  · rw [hv hr']
  · exact h.1 r' hr'

theorem Agree.setFlags {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (p : Bool)
    (c₁ o₁ z₁ f₁ c₂ o₂ z₂ f₂ : Option Bool)
    (hf : p = true → c₁ = c₂ ∧ z₁ = z₂ ∧ f₁ = f₂ ∧ o₁ = o₂) :
    ({ t with flags := p } : TState).Agree (X86.setFlags s₁ c₁ o₁ z₁ f₁) (X86.setFlags s₂ c₂ o₂ z₂ f₂) :=
  ⟨fun r hr => h.1 r hr, fun hp => by simpa [X86.setFlags] using hf hp, h.2.2⟩

theorem Agree.mem {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (m₁ m₂ : Mem) :
    t.Agree { s₁ with mem := m₁ } { s₂ with mem := m₂ } := ⟨h.1, h.2.1, h.2.2⟩

theorem Agree.weaken_flags {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (p : Bool)
    (hp : p = true → t.flags = true) : ({ t with flags := p } : TState).Agree s₁ s₂ :=
  ⟨h.1, fun hf => h.2.1 (hp hf), h.2.2⟩

theorem readSrc_agree {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (w : Nat) (src : Src) (b : Bool)
    (hb : t.srcPub src = some b) (v₁ v₂ : BitVec w) (h1 : readSrc s₁ w src = some v₁)
    (h2 : readSrc s₂ w src = some v₂) : b = true → v₁ = v₂ := by
  intro hbt
  cases src with
  | reg r =>
    simp only [srcPub, Option.some.injEq] at hb; subst hb
    simp only [readSrc, Option.some.injEq] at h1 h2
    rw [← h1, ← h2, h.readW w r hbt]
  | imm v =>
    simp only [readSrc, Option.some.injEq] at h1 h2
    rw [← h1, ← h2]
  | mem m =>
    simp only [srcPub] at hb
    split at hb <;> simp_all

end TState

open TState in
theorem execAlu_sound (w : Nat) (op : AluOp) (dst : Reg) (src : Src) (t t' : TState) (s₁ s₂ s₁' s₂' : State)
    {sz : Sz} (hstep : t.step (.alu op sz dst src) = some t') (hag : t.Agree s₁ s₂)
    (h1 : execAlu w op dst src s₁ = some s₁') (h2 : execAlu w op dst src s₂ = some s₂') :
    t'.Agree s₁' s₂' := by
  simp only [step] at hstep
  cases hb : t.srcPub src with
  | none => rw [hb] at hstep; cases hstep
  | some b =>
    rw [hb, Option.map_some, Option.some.injEq] at hstep
    subst hstep
    unfold execAlu at h1 h2
    cases hv1 : readSrc s₁ w src with
    | none => rw [hv1] at h1; cases h1
    | some v₁ =>
      cases hv2 : readSrc s₂ w src with
      | none => rw [hv2] at h2; cases h2
      | some v₂ =>
        rw [hv1, Option.bind_some] at h1
        rw [hv2, Option.bind_some] at h2
        have hv := readSrc_agree hag w src b hb v₁ v₂ hv1 hv2
        have ha : t.pub dst = true → s₁.readW w dst = s₂.readW w dst := hag.readW w dst
        cases op <;> simp only [Option.some.injEq] at h1 h2 <;> dsimp only at h1 h2 ⊢
        -- add, sub, and, or, xor
        case add | sub | and | or | xor =>
          subst h1; subst h2; unfold arithFlags
          refine Agree.writeW (Agree.setFlags hag _ _ _ _ _ _ _ _ _ ?_) _ _ _ _ ?_ <;>
          · intro hp
            simp only [Bool.and_eq_true, Bool.and_true] at hp
            rw [hv hp.1, ha hp.2]; try simp
        case cmp | test =>
          subst h1; subst h2; unfold arithFlags
          refine Agree.setFlags hag _ _ _ _ _ _ _ _ _ ?_
          intro hp
          simp only [Bool.and_eq_true, Bool.and_true] at hp
          rw [hv hp.1, ha hp.2]; simp
        case adc | sbb =>
          cases hc1 : s₁.cf with
          | none => rw [hc1] at h1; cases h1
          | some c₁ =>
            cases hc2 : s₂.cf with
            | none => rw [hc2] at h2; cases h2
            | some c₂ =>
              rw [hc1] at h1; rw [hc2] at h2
              simp only [Option.map_some, Option.some.injEq] at h1 h2
              subst h1; subst h2; unfold arithFlags
              refine Agree.writeW (Agree.setFlags hag _ _ _ _ _ _ _ _ _ ?_) _ _ _ _ ?_ <;>
              · intro hp
                simp only [Bool.and_eq_true] at hp
                have hc : c₁ = c₂ := by
                  have := (hag.2.1 hp.2).1; rw [hc1, hc2] at this; exact Option.some.inj this
                rw [hv hp.1.1, ha hp.1.2, hc]; try simp

theorem execV_frame (i : Instr) (s s' : State) (h : execV i s = some s') :
    s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of ∧ s'.labels = s.labels := by
  cases i <;> simp only [execV, State.setX, State.setV, State.storeW, readVSrc, Option.map] at h <;>
    (try split at h) <;> (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;> (try exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) <;> (try cases h)

open TState in
theorem execW_sound (w : Nat) (bs : BitVec w → BitVec w) (i : Instr) (t t' : TState)
    (s₁ s₂ s₁' s₂' : State) (hstep : t.step i = some t') (hag : t.Agree s₁ s₂)
    (h1 : execW w bs i s₁ = some s₁') (h2 : execW w bs i s₂ = some s₂') : t'.Agree s₁' s₂' := by
  cases i with
  | alu op sz dst src => exact execAlu_sound w op dst src t t' s₁ s₂ s₁' s₂' hstep hag h1 h2
  | mov sz dst src =>
    simp only [step] at hstep
    cases hb : t.srcPub src with
    | none => rw [hb] at hstep; cases hstep
    | some b =>
      rw [hb, Option.map_some, Option.some.injEq] at hstep; subst hstep
      simp only [execW] at h1 h2
      cases hv1 : readSrc s₁ w src with
      | none => rw [hv1] at h1; cases h1
      | some v₁ =>
        cases hv2 : readSrc s₂ w src with
        | none => rw [hv2] at h2; cases h2
        | some v₂ =>
          rw [hv1, Option.map_some, Option.some.injEq] at h1
          rw [hv2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          exact hag.writeW _ _ _ _ (readSrc_agree hag w src b hb v₁ v₂ hv1 hv2)
  | store sz m src =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [execW, State.storeW] at h1 h2
      split at h1 <;> split at h2 <;> simp_all
      subst h1; subst h2; exact hag.mem _ _
    · cases hstep
  | lea sz dst m =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.writeW _ _ _ _ (fun h => by rw [hag.ea m h])
  | rorx sz dst src n =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.writeW _ _ _ _ (fun h => by rw [hag.readW w src h])
  | andn sz dst s1 s2 =>
    simp only [step] at hstep
    cases hb : t.srcPub s2 with
    | none => rw [hb] at hstep; cases hstep
    | some b =>
      rw [hb, Option.map_some, Option.some.injEq] at hstep; subst hstep
      simp only [execW] at h1 h2
      cases hv1 : readSrc s₁ w s2 with
      | none => rw [hv1] at h1; cases h1
      | some v₁ =>
        cases hv2 : readSrc s₂ w s2 with
        | none => rw [hv2] at h2; cases h2
        | some v₂ =>
          rw [hv1, Option.map_some, Option.some.injEq] at h1
          rw [hv2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          have hv := readSrc_agree hag w s2 b hb v₁ v₂ hv1 hv2
          unfold arithFlags
          refine Agree.writeW (Agree.setFlags hag _ _ _ _ _ _ _ _ _ ?_) _ _ _ _ ?_ <;>
          · intro hp
            simp only [Bool.and_eq_true] at hp
            rw [hv hp.1, hag.readW w s1 hp.2]; try simp
  | shift op sz dst n =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, execShift] at h1 h2
    split at h1
    · -- zero count: the flags are unchanged, the destination is rewritten (zero-extended)
      rename_i hz
      rw [if_pos hz] at h2
      cases h1; cases h2
      refine Agree.writeW (t := { t with flags := t.pub dst && t.flags })
        (hag.weaken_flags _ (fun hf => by simp only [Bool.and_eq_true] at hf; exact hf.2)) _ _ _ _ ?_
      intro hp; rw [hag.readW w dst hp]
    · rename_i hz
      rw [if_neg hz] at h2
      have hd : t.pub dst = true → s₁.readW w dst = s₂.readW w dst := hag.readW w dst
      cases op <;> simp only [Option.some.injEq] at h1 h2 <;> subst h1 <;> subst h2
      all_goals
        refine Agree.writeW (t := { t with flags := t.pub dst && t.flags }) ?_ _ _ _ _ ?_
        · refine ⟨fun r hr => hag.1 r hr, fun hf => ?_, hag.2.2⟩
          simp only [Bool.and_eq_true] at hf
          obtain ⟨hp, hfl⟩ := hf
          obtain ⟨hc, hz, hs, ho⟩ := hag.2.1 hfl
          simp only [X86.setFlags]
          rw [hd hp]
          simp_all
        · intro hp; rw [hd hp]
  | not sz dst =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.writeW _ _ _ _ (fun h => by rw [hag.readW w dst h])
  | bswap sz dst =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.writeW _ _ _ _ (fun h => by rw [hag.readW w dst h])
  | movbe sz dst m =>
    simp only [step] at hstep
    split at hstep
    · simp only [Option.some.injEq] at hstep; subst hstep
      simp only [execW] at h1 h2
      cases hv1 : s₁.loadW w (s₁.ea m) with
      | none => rw [hv1] at h1; cases h1
      | some v₁ =>
        cases hv2 : s₂.loadW w (s₂.ea m) with
        | none => rw [hv2] at h2; cases h2
        | some v₂ =>
          rw [hv1, Option.map_some, Option.some.injEq] at h1
          rw [hv2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          exact hag.writeW _ _ _ _ (fun h => by cases h)
    · cases hstep
  | push r =>
    simp only [step] at hstep
    split at hstep
    · rename_i hsp
      simp only [Option.some.injEq] at hstep; subst hstep
      simp only [execW, State.storeW] at h1 h2
      split at h1 <;> split at h2 <;> simp only [Option.map_some, Option.map_none, reduceCtorEq,
        Option.some.injEq] at h1 h2
      subst h1; subst h2
      refine ⟨fun r' hr' => ?_, hag.2.1, hag.2.2⟩
      simp only [State.setReg, Regs.get_set]
      split_ifs with he
      · subst he; simp only [State.getReg]; rw [hag.1 _ hsp]
      · exact hag.1 r' hr'
    · cases hstep
  | pop r =>
    simp only [step] at hstep
    split at hstep
    · rename_i hsp
      simp only [Option.some.injEq] at hstep; subst hstep
      simp only [execW] at h1 h2
      cases hv1 : s₁.loadW 64 (s₁.getReg .rsp) with
      | none => rw [hv1] at h1; cases h1
      | some v₁ =>
        cases hv2 : s₂.loadW 64 (s₂.getReg .rsp) with
        | none => rw [hv2] at h2; cases h2
        | some v₂ =>
          rw [hv1, Option.map_some, Option.some.injEq] at h1
          rw [hv2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          have h1 := hag.writeW (w := 64) .rsp true (s₁.getReg .rsp + 8) (s₂.getReg .rsp + 8)
            (fun _ => by simp [hag.1 _ hsp])
          have h2 := h1.writeW (w := 64) r false v₁ v₂ (fun h => by cases h)
          simpa [State.writeW, State.setReg] using h2
    · cases hstep
  | mulx hi lo src =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    have hp : (t.pub .rdx && t.pub src) = true →
        (s₁.getReg .rdx).toNat * (s₁.getReg src).toNat = (s₂.getReg .rdx).toNat * (s₂.getReg src).toNat := by
      intro h
      simp only [Bool.and_eq_true] at h
      simp only [State.getReg, hag.1 _ h.1, hag.1 _ h.2]
    have a1 := hag.writeW (w := 64) lo (t.pub .rdx && t.pub src)
      (BitVec.ofNat 64 ((s₁.getReg .rdx).toNat * (s₁.getReg src).toNat))
      (BitVec.ofNat 64 ((s₂.getReg .rdx).toNat * (s₂.getReg src).toNat)) (fun h => by rw [hp h])
    have a2 := a1.writeW (w := 64) hi (t.pub .rdx && t.pub src)
      (BitVec.ofNat 64 ((s₁.getReg .rdx).toNat * (s₁.getReg src).toNat / 2 ^ 64))
      (BitVec.ofNat 64 ((s₂.getReg .rdx).toNat * (s₂.getReg src).toNat / 2 ^ 64)) (fun h => by rw [hp h])
    simpa [State.writeW, State.setReg] using a2
  | movabs dst v =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    have a1 := hag.writeW (w := 64) dst true v v (fun _ => rfl)
    simpa [State.writeW, State.setReg] using a1
  | vload128 _ m | vload256 _ m | vstore256 m _ | vinserti128hi _ _ m | vbroadcasti128 _ m
  | vpshufb _ _ _ | vpxor _ _ _ | vpalignr _ _ _ _ | vpsrld _ _ _ | vpslld _ _ _ | vpsrlq _ _ _
  | vpshufd _ _ _ | vzeroupper | vpaddd _ _ _
  | movdquLd _ _ | movdquSt _ _ | movdqa _ _ | paddd _ _ | pshufb _ _ | pshufd _ _ _ | palignr _ _ _
  | punpcklqdq _ _ | punpckhqdq _ _ | sha256rnds2 _ _ | sha256msg1 _ _ | sha256msg2 _ _ =>
    have ht : t' = t := by
      simp only [step] at hstep
      (try split at hstep) <;> simp_all
    subst ht
    simp only [execW] at h1 h2
    obtain ⟨g1, c1, z1, f1, o1, l1⟩ := execV_frame _ _ _ h1
    obtain ⟨g2, c2, z2, f2, o2, l2⟩ := execV_frame _ _ _ h2
    refine ⟨fun r hr => by rw [g1, g2]; exact hag.1 r hr, fun hf => ?_, by rw [l1, l2]; exact hag.2.2⟩
    rw [c1, c2, z1, z2, f1, f2, o1, o2]; exact hag.2.1 hf
  | inc sz dst | dec sz dst =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [execW, Option.some.injEq] at h1 h2; subst h1; subst h2
    have hd : t.pub dst = true → s₁.readW w dst = s₂.readW w dst := hag.readW w dst
    refine Agree.writeW (t := { t with flags := t.pub dst && t.flags }) ?_ _ _ _ _ ?_
    · refine ⟨fun r hr => hag.1 r hr, fun hf => ?_, hag.2.2⟩
      simp only [Bool.and_eq_true] at hf
      obtain ⟨hp, hfl⟩ := hf
      obtain ⟨hc, hz, hs, ho⟩ := hag.2.1 hfl
      rw [hd hp]
      simp_all
    · intro hp; rw [hd hp]

open TState in
theorem exec_sound (i : Instr) (t t' : TState) (s₁ s₂ s₁' s₂' : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) (h1 : exec i s₁ = some s₁') (h2 : exec i s₂ = some s₂') : t'.Agree s₁' s₂' := by
  unfold exec at h1 h2
  cases hsz : i.sz <;> rw [hsz] at h1 h2
  · exact execW_sound 32 bswap32 i t t' s₁ s₂ s₁' s₂' hstep hag h1 h2
  · exact execW_sound 64 bswap64 i t t' s₁ s₂ s₁' s₂' hstep hag h1 h2

open TState in
theorem srcAddrs_eq (t : TState) (s₁ s₂ : State) (hag : t.Agree s₁ s₂) (src : Src) (b : Bool)
    (hb : t.srcPub src = some b) : srcAddrs s₁ src = srcAddrs s₂ src := by
  cases src with
  | mem m =>
    simp only [srcPub] at hb
    split at hb
    · rename_i hm; simp only [srcAddrs, hag.ea m hm]
    · cases hb
  | _ => rfl

open TState in
theorem addrs_sound (i : Instr) (t t' : TState) (s₁ s₂ : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) : addrs i s₁ = addrs i s₂ := by
  cases i with
  | mov sz dst src | alu op sz dst src | andn sz dst s1 src =>
    simp only [step] at hstep
    cases hb : t.srcPub src with
    | none => rw [hb] at hstep; cases hstep
    | some b => exact srcAddrs_eq t s₁ s₂ hag src b hb
  | store sz m src | movbe sz dst m =>
    simp only [step] at hstep
    split at hstep
    · rename_i hm; simp only [addrs, hag.ea m hm]
    · cases hstep
  | push r | pop r =>
    simp only [step] at hstep
    split at hstep
    · rename_i hsp; simp only [addrs, State.getReg, hag.1 _ hsp]
    · cases hstep
  | vload128 _ m | vload256 _ m | vstore256 m _ | vinserti128hi _ _ m | vbroadcasti128 _ m
  | movdquLd _ m | movdquSt m _ =>
    simp only [step] at hstep
    split at hstep
    · rename_i hm; simp only [addrs, hag.ea m hm]
    · cases hstep
  | vpaddd _ _ src =>
    cases src with
    | mem m =>
      simp only [step] at hstep
      split at hstep
      · rename_i hm; simp only [addrs, hag.ea m hm]
      · cases hstep
    | reg _ => rfl
  | _ => rfl

namespace TState

theorem le_sound (a b : TState) (s₁ s₂ : State) (h : a.le b = true) (hag : a.Agree s₁ s₂) :
    b.Agree s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun r hr => hag.1 r ?_, fun hf => hag.2.1 ?_, hag.2.2⟩
  · rcases h.1 r (mem_allRegs r) with h' | h'
    · rw [hr] at h'; cases h'
    · exact h'
  · rcases h.2 with h' | h'
    · rw [hf] at h'; cases h'
    · exact h'

theorem le_refl (a : TState) : a.le a = true := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  exact ⟨fun r _ => by cases a.pub r <;> simp, by cases a.flags <;> simp⟩

theorem le_join_left (a b : TState) : a.le (a.join b) = true := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun r _ => ?_, by cases ha : a.flags <;> cases hb : b.flags <;> simp [join, ha, hb]⟩
  rw [join_pub]; cases a.pub r <;> cases b.pub r <;> simp

theorem le_join_right (a b : TState) : b.le (a.join b) = true := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun r _ => ?_, by cases ha : a.flags <;> cases hb : b.flags <;> simp [join, ha, hb]⟩
  rw [join_pub]; cases a.pub r <;> cases b.pub r <;> simp

theorem cond_sound (c : Cond) (t : TState) (s₁ s₂ : State) (hc : t.condOk c = true)
    (hag : t.Agree s₁ s₂) : evalCond c s₁ = evalCond c s₂ := by
  obtain ⟨hcf, hzf, hsf, hof⟩ := hag.2.1 hc
  cases c <;> simp [evalCond, hcf, hzf]

end TState

/-- The x86-64 taint domain. -/
def taint : TaintDom isa where
  T := TState
  step := TState.step
  condOk := TState.condOk
  join := TState.join
  le := TState.le
  Agree := TState.Agree
  step_sound i t t' s₁ s₂ s₁' s₂' hs hag h1 h2 :=
    ⟨addrs_sound i t t' s₁ s₂ hs hag, exec_sound i t t' s₁ s₂ s₁' s₂' hs hag h1 h2⟩
  cond_sound := TState.cond_sound
  le_sound := TState.le_sound
  le_refl := TState.le_refl
  le_join_left := TState.le_join_left
  le_join_right := TState.le_join_right

end CC.X86
