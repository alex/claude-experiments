import ClaudeCrypto.Ppc.StateLemmas
import ClaudeCrypto.Framework.Taint

/-!
# Taint domain for ppc64le

Tracks, for each general-purpose register `r0`–`r31` and for the CR0 bits (as
a group), whether the value is *public*.  Memory contents are always treated
as secret, and the vector registers are not tracked at all: no modelled
instruction moves data from a vector register into a general-purpose
register, CR0, or an address, so they can never influence the leakage.
Every address computation must only use public registers.

The addresses of the program's data labels are public (they are fixed when
the program is loaded), so `Agree` requires them to be equal.  The link
register is not tracked: `adr` copies it into `r0`, which becomes secret.
-/

namespace CC.Ppc

/-- Abstract state: a bitmask of public GPRs (bit `r.idx`) and whether CR0 is
public.  (A bitmask keeps kernel evaluation of the analysis fast.) -/
structure TState where
  mask : Nat
  flags : Bool

def GReg.idx (r : GReg) : Nat := r.ctorIdx

theorem GReg.idx_lt (r : GReg) : r.idx < 32 := by cases r <;> decide

theorem GReg.idx_inj (r r' : GReg) : r.idx = r'.idx ↔ r = r' := by
  cases r <;> cases r' <;> decide

def allGRegs : List GReg :=
  [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15,
   .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem mem_allGRegs (r : GReg) : r ∈ allGRegs := by cases r <;> simp [allGRegs]

/-- `2^32 - 1`: all registers. -/
def fullMask : Nat := 4294967295

namespace TState

def pub (t : TState) (r : GReg) : Bool := t.mask.testBit r.idx

/-- `(RA|0)` is public: `RA = 0` denotes the constant 0. -/
def raPub (t : TState) (r : GReg) : Bool :=
  match r with
  | .r0 => true
  | _ => t.pub r

def setPub (t : TState) (r : GReg) (b : Bool) : TState :=
  { t with mask := if b then t.mask ||| (1 <<< r.idx) else t.mask &&& (fullMask ^^^ (1 <<< r.idx)) }

def step (i : Instr) (t : TState) : Option TState :=
  match i with
  | .lxvw4x _ ra rb | .stxvw4x _ ra rb => if t.raPub ra && t.pub rb then some t else none
  | .vadduwm .. | .vxor .. | .vor .. | .vsel .. | .vperm .. | .vsldoi .. | .vmrghw .. | .xxpermdi ..
  | .vshasigmaw .. => some t
  | .addi rt ra _ => some (t.setPub rt (t.raPub ra))
  | .neg rt ra => some (t.setPub rt (t.pub ra))
  | .cmpldi ra _ => some { t with flags := t.pub ra }
  | .adr rt _ => some ((t.setPub .r0 false).setPub rt true)
  | .add rt ra rb | .subf rt ra rb | .addc rt ra rb | .subfc rt ra rb | .mulld rt ra rb
  | .mulhdu rt ra rb | .and rt ra rb | .or rt ra rb | .xor rt ra rb =>
    some (t.setPub rt (t.pub ra && t.pub rb))
  | .adde rt _ _ | .subfe rt _ _ => some (t.setPub rt false)
  | .rldicl ra rs _ _ | .rldicr ra rs _ _ | .ori ra rs _ | .oris ra rs _ =>
    some (t.setPub ra (t.pub rs))
  | .ld rt ra _ => if t.raPub ra then some (t.setPub rt false) else none
  | .std _ ra _ => if t.raPub ra then some t else none
  | .ldx rt ra rb | .ldbrx rt ra rb => if t.raPub ra && t.pub rb then some (t.setPub rt false) else none
  | .stdx _ ra rb => if t.raPub ra && t.pub rb then some t else none

def condOk (_ : Cond) (t : TState) : Bool := t.flags

def join (a b : TState) : TState := ⟨a.mask &&& b.mask, a.flags && b.flags⟩

def le (a b : TState) : Bool := allGRegs.all (fun r => !b.pub r || a.pub r) && (!b.flags || a.flags)

theorem join_pub (a b : TState) (r : GReg) : (a.join b).pub r = (a.pub r && b.pub r) := by
  simp [join, pub, Nat.testBit_and]

/-- `s₁` and `s₂` agree on all public registers, (if public) CR0, and the
addresses of the data labels. -/
def Agree (t : TState) (s₁ s₂ : State) : Prop :=
  (∀ r, t.pub r = true → s₁.getG r = s₂.getG r) ∧
  (t.flags = true → s₁.lt = s₂.lt ∧ s₁.gt = s₂.gt ∧ s₁.eq = s₂.eq) ∧
  s₁.labels = s₂.labels

/-! ### Lemmas -/

theorem testBit_fullMask (r : GReg) : fullMask.testBit r.idx = true := by cases r <;> decide

theorem setPub_pub (t : TState) (r r' : GReg) (b : Bool) :
    (t.setPub r b).pub r' = if r' = r then b else t.pub r' := by
  have hi := GReg.idx_inj r' r
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

theorem Agree.raOr0 {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : GReg) (hr : t.raPub r = true) :
    s₁.raOr0 r = s₂.raOr0 r := by
  cases r <;> first | rfl | exact h.1 _ hr

theorem Agree.setG {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : GReg) (b : Bool)
    (v₁ v₂ : BitVec 64) (hv : b = true → v₁ = v₂) :
    (t.setPub r b).Agree (s₁.setG r v₁) (s₂.setG r v₂) := by
  refine ⟨fun r' hr' => ?_, fun hf => h.2.1 hf, h.2.2⟩
  rw [State.getG_setG, State.getG_setG]
  rw [setPub_pub] at hr'
  split_ifs at hr' ⊢ with he
  · rw [hv hr']
  · exact h.1 r' hr'

theorem Agree.setV {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : VReg) (v₁ v₂ : BitVec 128) :
    t.Agree (s₁.setV r v₁) (s₂.setV r v₂) := ⟨h.1, h.2.1, h.2.2⟩

theorem Agree.mem {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (m₁ m₂ : Mem) :
    t.Agree { s₁ with mem := m₁ } { s₂ with mem := m₂ } := ⟨h.1, h.2.1, h.2.2⟩

theorem Agree.setGCA {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (r : GReg) (b : Bool)
    (p₁ p₂ : BitVec 64 × Bool) (hv : b = true → p₁.1 = p₂.1) :
    (t.setPub r b).Agree (s₁.setGCA r p₁) (s₂.setGCA r p₂) :=
  let h' := h.setG r b p₁.1 p₂.1 hv
  ⟨h'.1, h'.2.1, h'.2.2⟩

theorem ea_eq {t : TState} {s₁ s₂ : State} (h : t.Agree s₁ s₂) (ra rb : GReg)
    (hp : (t.raPub ra && t.pub rb) = true) : s₁.ea ra rb = s₂.ea ra rb := by
  simp only [Bool.and_eq_true] at hp
  simp only [State.ea, h.raOr0 ra hp.1, h.1 rb hp.2]

end TState

open TState in
theorem exec_sound (i : Instr) (t t' : TState) (s₁ s₂ s₁' s₂' : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) (h1 : exec i s₁ = some s₁') (h2 : exec i s₂ = some s₂') : t'.Agree s₁' s₂' := by
  cases i with
  | lxvw4x v ra rb =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec] at h1 h2
      split at h1 <;> split at h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.setV _ _ _
    · cases hstep
  | stxvw4x v ra rb =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec] at h1 h2
      split at h1 <;> split at h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.mem _ _
    · cases hstep
  | vadduwm | vxor | vor | vsel | vperm | vsldoi | vmrghw | xxpermdi | vshasigmaw =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setV _ _ _
  | addi rt ra si =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setG _ _ _ _ (fun hp => by rw [hag.raOr0 ra hp])
  | neg rt ra =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setG _ _ _ _ (fun hp => by rw [hag.1 ra hp])
  | cmpldi ra ui =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    refine ⟨hag.1, fun hp => ?_, hag.2.2⟩
    change t.pub ra = true at hp
    have e := hag.1 ra hp
    exact ⟨by rw [e], by rw [e], by rw [e]⟩
  | add rt ra rb | subf rt ra rb | mulld rt ra rb | mulhdu rt ra rb | and rt ra rb | or rt ra rb
  | xor rt ra rb =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    refine hag.setG _ _ _ _ (fun hp => ?_)
    simp only [Bool.and_eq_true] at hp
    rw [hag.1 ra hp.1, hag.1 rb hp.2]
  | addc rt ra rb | subfc rt ra rb =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    refine hag.setGCA _ _ _ _ (fun hp => ?_)
    simp only [Bool.and_eq_true] at hp
    rw [hag.1 ra hp.1, hag.1 rb hp.2]
  | adde rt ra rb | subfe rt ra rb =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec] at h1 h2
    cases hc1 : s₁.ca with
    | none => rw [hc1] at h1; cases h1
    | some c₁ =>
      cases hc2 : s₂.ca with
      | none => rw [hc2] at h2; cases h2
      | some c₂ =>
        rw [hc1, Option.map_some, Option.some.injEq] at h1
        rw [hc2, Option.map_some, Option.some.injEq] at h2
        subst h1; subst h2
        exact hag.setGCA _ _ _ _ (fun h => by cases h)
  | rldicl ra rs sh mb | rldicr ra rs sh mb =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec] at h1 h2
    split at h1
    · simp only [Option.some.injEq] at h1; subst h1
      rw [if_pos (by assumption), Option.some.injEq] at h2; subst h2
      exact hag.setG _ _ _ _ (fun hp => by rw [hag.1 rs hp])
    · cases h1
  | ori ra rs ui | oris ra rs ui =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    simp only [exec, Option.some.injEq] at h1 h2; subst h1; subst h2
    exact hag.setG _ _ _ _ (fun hp => by rw [hag.1 rs hp])
  | ld rt ra ds =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec, State.load64] at h1 h2
      split at h1 <;> split at h2 <;>
        simp only [reduceCtorEq, Option.map_some, Option.map_none, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.setG _ _ _ _ (fun h => by cases h)
    · cases hstep
  | ldx rt ra rb | ldbrx rt ra rb =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec, State.load64] at h1 h2
      split at h1 <;> split at h2 <;>
        simp only [reduceCtorEq, Option.map_some, Option.map_none, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.setG _ _ _ _ (fun h => by cases h)
    · cases hstep
  | std rx ra ds | stdx rx ra ds =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [exec, State.store64] at h1 h2
      split at h1 <;> split at h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hag.mem _ _
    · cases hstep
  | adr rt l =>
    simp only [step, Option.some.injEq] at hstep; subst hstep
    cases rt <;> simp only [exec, Option.some.injEq, reduceCtorEq] at h1 h2 <;>
    · subst h1; subst h2
      exact (hag.setG .r0 false _ _ (fun h => by cases h)).setG _ true _ _ (fun _ => by rw [hag.2.2])

open TState in
theorem addrs_sound (i : Instr) (t t' : TState) (s₁ s₂ : State) (hstep : t.step i = some t')
    (hag : t.Agree s₁ s₂) : addrs i s₁ = addrs i s₂ := by
  cases i with
  | lxvw4x _ ra rb | stxvw4x _ ra rb | ldx _ ra rb | stdx _ ra rb | ldbrx _ ra rb =>
    simp only [step] at hstep
    split at hstep
    · rename_i hp; simp only [addrs, ea_eq hag ra rb hp]
    · cases hstep
  | ld _ ra ds | std _ ra ds =>
    simp only [step] at hstep
    split at hstep
    · rename_i hp; simp only [addrs, hag.raOr0 ra hp]
    · cases hstep
  | _ => rfl

namespace TState

theorem le_sound (a b : TState) (s₁ s₂ : State) (h : a.le b = true) (hag : a.Agree s₁ s₂) :
    b.Agree s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun r hr => hag.1 r ?_, fun hf => hag.2.1 ?_, hag.2.2⟩
  · rcases h.1 r (mem_allGRegs r) with h' | h'
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
  obtain ⟨_, _, he⟩ := hag.2.1 hc
  cases c <;> simp [evalCond, he]

end TState

/-- The ppc64le taint domain. -/
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

end CC.Ppc
