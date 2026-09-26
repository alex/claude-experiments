import ClaudeCrypto.Arm.StateLemmas
import ClaudeCrypto.Framework.Taint

/-!
# Taint domain for AArch64

Tracks, for each general-purpose register `X0`–`X30` and for the NZCV flags
(as a group), whether the value is *public*.  Memory contents are always
treated as secret, and the vector registers are not tracked at all: no
modelled instruction moves data from a vector register into a general-purpose
register, the flags, or an address, so they can never influence the leakage.
Every address computation must only use public registers.

The addresses of the program's data labels are public (they are fixed when
the program is loaded), so `Agree` requires them to be equal.
-/

namespace CC.Arm

/-- Abstract state: a bitmask of public X registers (bit `r.idx`) and whether
the flags are public.  (A bitmask keeps kernel evaluation of the analysis fast.) -/
structure TState where
  mask : Nat
  flags : Bool

def XReg.idx (r : XReg) : Nat := r.ctorIdx

theorem XReg.idx_lt (r : XReg) : r.idx < 31 := by cases r <;> decide

theorem XReg.idx_inj (r r' : XReg) : r.idx = r'.idx ↔ r = r' := by
  cases r <;> cases r' <;> decide

def allXRegs : List XReg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
   .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30]

theorem mem_allXRegs (r : XReg) : r ∈ allXRegs := by cases r <;> simp [allXRegs]

/-- `2^31 - 1`: all registers. -/
def fullMask : Nat := 2147483647

namespace TState

def pub (t : TState) (r : XReg) : Bool := t.mask.testBit r.idx

def setPub (t : TState) (r : XReg) (b : Bool) : TState :=
  { t with mask := if b then t.mask ||| (1 <<< r.idx) else t.mask &&& (fullMask ^^^ (1 <<< r.idx)) }

def step (i : Instr) (t : TState) : Option TState :=
  match i with
  | .ldrq _ n _ | .strq _ n _ => if t.pub n then some t else none
  | .ld1 _ _ n _ | .st1 _ _ n _ => if t.pub n then some t else none
  | .rev32 .. | .addv .. | .movv .. | .sha256h .. | .sha256h2 .. | .sha256su0 .. | .sha256su1 .. =>
    some t
  | .adr d _ => some (t.setPub d true)
  | .addi d n _ | .subi d n _ | .mov d n => some (t.setPub d (t.pub n))
  | .subsi d n _ => some (({ t with flags := t.pub n }).setPub d (t.pub n))
  | .addr d n m | .subr d n m | .mul d n m | .umulh d n m | .and d n m | .orr d n m | .eor d n m =>
    some (t.setPub d (t.pub n && t.pub m))
  | .adds d n m | .subs d n m =>
    some (({ t with flags := t.pub n && t.pub m }).setPub d (t.pub n && t.pub m))
  | .adcs d n m | .sbcs d n m =>
    some (({ t with flags := t.pub n && t.pub m && t.flags }).setPub d (t.pub n && t.pub m && t.flags))
  | .lsl d n _ | .lsr d n _ | .rev d n => some (t.setPub d (t.pub n))
  | .movz d _ _ => some (t.setPub d true)
  | .movk d _ _ => some (t.setPub d (t.pub d))
  | .csetm d _ => some (t.setPub d t.flags)
  | .ldr d n _ => if t.pub n then some (t.setPub d false) else none
  | .ldrr d n m => if t.pub n && t.pub m then some (t.setPub d false) else none
  | .str _ n _ => if t.pub n then some t else none
  | .strr _ n m => if t.pub n && t.pub m then some t else none

def condOk (c : Cond) (t : TState) : Bool :=
  match c with
  | .cbz r | .cbnz r => t.pub r
  | _ => t.flags

def join (a b : TState) : TState := ⟨a.mask &&& b.mask, a.flags && b.flags⟩

def le (a b : TState) : Bool := allXRegs.all (fun r => !b.pub r || a.pub r) && (!b.flags || a.flags)

theorem join_pub (a b : TState) (r : XReg) : (a.join b).pub r = (a.pub r && b.pub r) := by
  simp [join, pub, Nat.testBit_and]

/-- `s₁` and `s₂` agree on all public registers, (if public) the flags, and the
addresses of the data labels. -/
def Agree (t : TState) (s₁ s₂ : State) : Prop :=
  (∀ r, t.pub r = true → s₁.getX r = s₂.getX r) ∧
  (t.flags = true → s₁.nf = s₂.nf ∧ s₁.zf = s₂.zf ∧ s₁.cf = s₂.cf ∧ s₁.vf = s₂.vf) ∧
  s₁.labels = s₂.labels

/-! ### Lemmas -/

theorem testBit_fullMask (r : XReg) : fullMask.testBit r.idx = true := by cases r <;> decide

theorem setPub_pub (t : TState) (r r' : XReg) (b : Bool) :
    (t.setPub r b).pub r' = if r' = r then b else t.pub r' := by
  have h1 := XReg.idx_lt r; have h2 := XReg.idx_lt r'
  have hi := XReg.idx_inj r' r
  unfold setPub pub
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_and, Nat.testBit_xor, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    by_cases h : r' = r
    · subst h; simp [testBit_fullMask]
    · have : r.idx ≠ r'.idx := fun e => h (hi.mp e.symm)
      simp [h, this, testBit_fullMask]
  · simp only [↓reduceIte, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : r' = r
    · subst h; simp
    · have : r.idx ≠ r'.idx := fun e => h (hi.mp e.symm)
      simp [h, this]

theorem Agree.setX {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : XReg) (b : Bool)
    (v₁ v₂ : BitVec 64) (hv : b = true → v₁ = v₂) :
    (t.setPub r b).Agree (s₁.setX r v₁) (s₂.setX r v₂) := by
  refine ⟨fun r' hr' => ?_, fun hf => h.2.1 hf, h.2.2⟩
  rw [State.getX_setX, State.getX_setX]
  rw [setPub_pub] at hr'
  split_ifs at hr' ⊢ with he
  · rw [hv hr']
  · exact h.1 r' hr'

theorem Agree.setV {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : VReg) (v₁ v₂ : BitVec 128) :
    t.Agree (s₁.setV r v₁) (s₂.setV r v₂) := ⟨h.1, h.2.1, h.2.2⟩

theorem Agree.mem {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (m₁ m₂ : Mem) :
    t.Agree { s₁ with mem := m₁ } { s₂ with mem := m₂ } := ⟨h.1, h.2.1, h.2.2⟩

theorem Agree.setNZCV {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (d : XReg) (p : Bool)
    (r₁ r₂ : BitVec 64 × Bool × Bool × Bool × Bool) (hr : p = true → r₁ = r₂) :
    ({ t with flags := p }.setPub d p).Agree (s₁.setNZCV d r₁) (s₂.setNZCV d r₂) := by
  apply Agree.setX (t := { t with flags := p })
  · refine ⟨h.1, fun hp => ?_, h.2.2⟩
    simp only [hr hp, and_self]
  · intro hp; rw [hr hp]

theorem Agree.flags_eq {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (hf : t.flags = true) (c : Cond) :
    condHolds c s₁ = condHolds c s₂ := by
  obtain ⟨_, hz, hc, _⟩ := h.2.1 hf
  cases c <;> simp [condHolds, hz, hc]

theorem ld1Regs_agree {t : TState} (ts : List VReg) : ∀ (s₁ s₂ s₁' s₂' : State) (a₁ a₂ : Addr) (i : Nat),
    t.Agree s₁ s₂ → s₁.ld1Regs a₁ i ts = some s₁' → s₂.ld1Regs a₂ i ts = some s₂' →
    t.Agree s₁' s₂' ∧ s₁'.x = s₁.x ∧ s₂'.x = s₂.x := by
  induction ts with
  | nil =>
    intro s₁ s₂ s₁' s₂' a₁ a₂ i h h1 h2
    simp only [State.ld1Regs, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact ⟨h, rfl, rfl⟩
  | cons v ts ih =>
    intro s₁ s₂ s₁' s₂' a₁ a₂ i h h1 h2
    simp only [State.ld1Regs] at h1 h2
    cases hx1 : s₁.loadW 128 (a₁ + BitVec.ofNat 64 (16 * i)) with
    | none => rw [hx1] at h1; cases h1
    | some x₁ =>
      cases hx2 : s₂.loadW 128 (a₂ + BitVec.ofNat 64 (16 * i)) with
      | none => rw [hx2] at h2; cases h2
      | some x₂ =>
        rw [hx1, Option.bind_some] at h1; rw [hx2, Option.bind_some] at h2
        obtain ⟨hag, e1, e2⟩ := ih (s₁.setV v x₁) (s₂.setV v x₂) _ _ _ _ _ (h.setV v x₁ x₂) h1 h2
        exact ⟨hag, e1, e2⟩

theorem st1Regs_agree {t : TState} (ts : List VReg) : ∀ (s₁ s₂ s₁' s₂' : State) (a₁ a₂ : Addr) (i : Nat),
    t.Agree s₁ s₂ → s₁.st1Regs a₁ i ts = some s₁' → s₂.st1Regs a₂ i ts = some s₂' →
    t.Agree s₁' s₂' ∧ s₁'.x = s₁.x ∧ s₂'.x = s₂.x := by
  induction ts with
  | nil =>
    intro s₁ s₂ s₁' s₂' a₁ a₂ i h h1 h2
    simp only [State.st1Regs, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact ⟨h, rfl, rfl⟩
  | cons v ts ih =>
    intro s₁ s₂ s₁' s₂' a₁ a₂ i h h1 h2
    simp only [State.st1Regs, State.storeW] at h1 h2
    split at h1
    · split at h2
      · rw [Option.bind_some] at h1 h2
        exact ih { s₁ with mem := s₁.mem.writeW (a₁ + BitVec.ofNat 64 (16 * i)) (s₁.getV v) }
          { s₂ with mem := s₂.mem.writeW (a₂ + BitVec.ofNat 64 (16 * i)) (s₂.getV v) } _ _ _ _ _
          (h.mem _ _) h1 h2
      · cases h2
    · cases h1

theorem Agree.ldst {t : TState} {s₁ s₂ u₁ u₂ : State} (h : t.Agree s₁ s₂) (n : XReg) (hn : t.pub n = true)
    (hag : t.Agree u₁ u₂) (e1 : u₁.x = s₁.x) (e2 : u₂.x = s₂.x) (post : Bool) (k : Nat) :
    t.Agree (if post then u₁.setX n (s₁.getX n + BitVec.ofNat 64 k) else u₁)
      (if post then u₂.setX n (s₂.getX n + BitVec.ofNat 64 k) else u₂) := by
  cases post
  · exact hag
  · simp only [ite_true]
    have := hag.setX n true (s₁.getX n + BitVec.ofNat 64 k) (s₂.getX n + BitVec.ofNat 64 k)
      (fun _ => by rw [h.1 n hn])
    have hp : t.setPub n true = t := by
      cases t with
      | mk mask flags =>
        simp only [setPub, ↓reduceIte, TState.mk.injEq, and_true]
        apply Nat.eq_of_testBit_eq; intro j
        simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
        by_cases hj : n.idx = j
        · subst hj; simp only [pub] at hn; simp [hn]
        · simp [hj]
    rwa [hp] at this

end TState

open TState in
theorem exec_sound (i : Instr) (t t' : TState) (s₁ s₂ s₁' s₂' : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) (h1 : exec i s₁ = some s₁') (h2 : exec i s₂ = some s₂') : t'.Agree s₁' s₂' := by
  cases i with
  | ldrq v n off | strq v n off =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec, State.storeW] at h1 h2
      first
      | (cases hx1 : s₁.loadW 128 (s₁.getX n + BitVec.ofNat 64 off) with
          | none => rw [hx1] at h1; cases h1
          | some x₁ =>
            cases hx2 : s₂.loadW 128 (s₂.getX n + BitVec.ofNat 64 off) with
            | none => rw [hx2] at h2; cases h2
            | some x₂ =>
              rw [hx1, Option.map_some, Option.some.injEq] at h1
              rw [hx2, Option.map_some, Option.some.injEq] at h2
              subst h1; subst h2; exact hag.setV _ _ _)
      | (split at h1 <;> split at h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h1 h2
         subst h1; subst h2; exact hag.mem _ _)
    · cases hstep
  | ld1 ts arr n post =>
    simp only [step] at hstep
    split at hstep
    · rename_i hn
      cases hstep
      simp only [exec] at h1 h2
      cases hx1 : s₁.ld1Regs (s₁.getX n) 0 ts with
      | none => rw [hx1] at h1; cases h1
      | some u₁ =>
        cases hx2 : s₂.ld1Regs (s₂.getX n) 0 ts with
        | none => rw [hx2] at h2; cases h2
        | some u₂ =>
          rw [hx1, Option.map_some, Option.some.injEq] at h1
          rw [hx2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          obtain ⟨hag', e1, e2⟩ := ld1Regs_agree ts _ _ _ _ _ _ _ hag hx1 hx2
          exact hag.ldst n hn hag' e1 e2 post _
    · cases hstep
  | st1 ts arr n post =>
    simp only [step] at hstep
    split at hstep
    · rename_i hn
      cases hstep
      simp only [exec] at h1 h2
      cases hx1 : s₁.st1Regs (s₁.getX n) 0 ts with
      | none => rw [hx1] at h1; cases h1
      | some u₁ =>
        cases hx2 : s₂.st1Regs (s₂.getX n) 0 ts with
        | none => rw [hx2] at h2; cases h2
        | some u₂ =>
          rw [hx1, Option.map_some, Option.some.injEq] at h1
          rw [hx2, Option.map_some, Option.some.injEq] at h2
          subst h1; subst h2
          obtain ⟨hag', e1, e2⟩ := st1Regs_agree ts _ _ _ _ _ _ _ hag hx1 hx2
          exact hag.ldst n hn hag' e1 e2 post _
    · cases hstep
  | rev32 | addv | movv | sha256h | sha256h2 | sha256su0 | sha256su1 =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setV _ _ _
  | adr d l =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setX _ _ _ _ (fun _ => by rw [hag.2.2])
  | addi d n imm | subi d n imm | mov d n =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setX _ _ _ _ (fun hp => by rw [hag.1 n hp])
  | subsi d n imm =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    apply Agree.setX
    · refine ⟨hag.1, fun hp => ?_, hag.2.2⟩
      change t.pub n = true at hp
      simp only [hag.1 n hp, and_self]
    · intro hp; rw [hag.1 n hp]

  | addr d n m | subr d n m | mul d n m | umulh d n m | and d n m | orr d n m | eor d n m =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    refine hag.setX _ _ _ _ (fun hp => ?_)
    simp only [Bool.and_eq_true] at hp
    rw [hag.1 n hp.1, hag.1 m hp.2]
  | adds d n m | subs d n m =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    refine hag.setNZCV _ _ _ _ (fun hp => ?_)
    simp only [Bool.and_eq_true] at hp
    rw [hag.1 n hp.1, hag.1 m hp.2]
  | adcs d n m | sbcs d n m =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec] at h1 h2
    cases hc1 : s₁.cf with
    | none => rw [hc1] at h1; cases h1
    | some c₁ =>
      cases hc2 : s₂.cf with
      | none => rw [hc2] at h2; cases h2
      | some c₂ =>
        rw [hc1, Option.map_some, Option.some.injEq] at h1
        rw [hc2, Option.map_some, Option.some.injEq] at h2
        subst h1; subst h2
        refine hag.setNZCV _ _ _ _ (fun hp => ?_)
        simp only [Bool.and_eq_true] at hp
        have hc := (hag.2.1 hp.2).2.2.1
        rw [hc1, hc2, Option.some.injEq] at hc
        rw [hag.1 n hp.1.1, hag.1 m hp.1.2, hc]
  | lsl d n sh | lsr d n sh | rev d n =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setX _ _ _ _ (fun hp => by rw [hag.1 n hp])
  | movz d imm hw =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setX _ _ _ _ (fun _ => rfl)
  | movk d imm hw =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setX _ _ _ _ (fun hp => by rw [hag.1 d hp])
  | csetm d c =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec] at h1 h2
    cases hc1 : condHolds c s₁ with
    | none => rw [hc1] at h1; cases h1
    | some b₁ =>
      cases hc2 : condHolds c s₂ with
      | none => rw [hc2] at h2; cases h2
      | some b₂ =>
        rw [hc1, Option.map_some, Option.some.injEq] at h1
        rw [hc2, Option.map_some, Option.some.injEq] at h2
        subst h1; subst h2
        refine hag.setX _ _ _ _ (fun hp => ?_)
        have := hag.flags_eq hp c
        rw [hc1, hc2, Option.some.injEq] at this
        rw [this]
  | ldr d n off | ldrr d n off =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec] at h1 h2
      first
      | (cases hx1 : s₁.loadW 64 (s₁.getX n + BitVec.ofNat 64 off) with
          | none => rw [hx1] at h1; cases h1
          | some x₁ =>
            cases hx2 : s₂.loadW 64 (s₂.getX n + BitVec.ofNat 64 off) with
            | none => rw [hx2] at h2; cases h2
            | some x₂ =>
              rw [hx1, Option.map_some, Option.some.injEq] at h1
              rw [hx2, Option.map_some, Option.some.injEq] at h2
              subst h1; subst h2; exact hag.setX _ _ _ _ (fun h => by cases h))
      | (cases hx1 : s₁.loadW 64 (s₁.getX n + s₁.getX off) with
          | none => rw [hx1] at h1; cases h1
          | some x₁ =>
            cases hx2 : s₂.loadW 64 (s₂.getX n + s₂.getX off) with
            | none => rw [hx2] at h2; cases h2
            | some x₂ =>
              rw [hx1, Option.map_some, Option.some.injEq] at h1
              rw [hx2, Option.map_some, Option.some.injEq] at h2
              subst h1; subst h2; exact hag.setX _ _ _ _ (fun h => by cases h))
    · cases hstep
  | str v n off | strr v n off =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec, State.storeW] at h1 h2
      split at h1 <;> split at h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.mem _ _
    · cases hstep

open TState in
theorem addrs_sound (i : Instr) (t t' : TState) (s₁ s₂ : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) : addrs i s₁ = addrs i s₂ := by
  cases i with
  | ldrq _ n _ | strq _ n _ | ld1 _ _ n _ | st1 _ _ n _ | ldr _ n _ | str _ n _ =>
    simp only [step] at hstep
    split at hstep
    · rename_i hn; simp only [addrs, hag.1 n hn]
    · cases hstep
  | ldrr _ n m | strr _ n m =>
    simp only [step] at hstep
    split at hstep
    · rename_i hn
      simp only [Bool.and_eq_true] at hn
      simp only [addrs, hag.1 n hn.1, hag.1 m hn.2]
    · cases hstep
  | _ => rfl

namespace TState

theorem le_sound (a b : TState) (s₁ s₂ : State) (h : a.le b = true) (hag : a.Agree s₁ s₂) :
    b.Agree s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun r hr => hag.1 r ?_, fun hf => hag.2.1 ?_, hag.2.2⟩
  · rcases h.1 r (mem_allXRegs r) with h' | h'
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
  cases c with
  | cbz r | cbnz r => simp only [condOk] at hc; simp only [evalCond, hag.1 r hc]
  | _ =>
    simp only [condOk] at hc
    obtain ⟨hn, hz, hc', hv⟩ := hag.2.1 hc
    simp [evalCond, hz, hc']

end TState

/-- The AArch64 taint domain. -/
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

end CC.Arm
