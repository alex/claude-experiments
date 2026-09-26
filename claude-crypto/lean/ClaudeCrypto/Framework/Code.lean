import ClaudeCrypto.Common.Mem

/-!
# Structured assembly programs

Every architecture model (x86-64, AArch64, ppc64le) instantiates `ISA`:
a machine state, a type of straight-line instructions with a (partial)
semantics, and a type of branch conditions.

Programs are written as `Code`: straight-line blocks of real instructions
glued together with structured control flow (`ite`, do-while `loop`).  The
printer (`Framework/Print.lean`) lowers structured control flow to labels and
conditional jumps in the obvious way.

## Semantics, safety and leakage

`Exec M c s t s'` means: running `c` from state `s` terminates in state `s'`
without faulting, producing the leakage trace `t`.  Instructions fault
(`exec` returns `none`) on any memory access outside the regions the state
permits, and on reading undefined flags; so a proof of `∃ t s', Exec M c s t s' ∧ …`
establishes termination, memory safety and functional correctness at once.

The leakage trace records every memory address accessed and every branch
decision: the standard "constant-time" leakage model.  Instructions whose
timing depends on operand values (e.g. division) are simply not part of any
ISA model.
-/

namespace CC

/-- One observation of the constant-time attacker. -/
inductive Leak where
  | addr (a : Addr)
  | branch (taken : Bool)
  deriving DecidableEq, Repr

/-- The interface between an architecture model and the generic framework. -/
structure ISA where
  State : Type
  Instr : Type
  Cond : Type
  /-- Semantics of a straight-line instruction; `none` means the machine faults. -/
  exec : Instr → State → Option State
  /-- The addresses of the memory accessed by an instruction. -/
  addrs : Instr → State → List Addr
  /-- Evaluate a branch condition; `none` if it depends on an undefined flag. -/
  eval : Cond → State → Option Bool

/-- Structured code. -/
inductive Code (I C : Type) where
  | block (is : List I)
  | seq (c₁ c₂ : Code I C)
  /-- `if c then t else e` -/
  | ite (c : C) (t e : Code I C)
  /-- `do body while c` -/
  | loop (body : Code I C) (c : C)

variable (M : ISA)

abbrev Prog := Code M.Instr M.Cond

/-- Run a straight-line block. -/
def execBlock : List M.Instr → M.State → Option (M.State × List Leak)
  | [], s => some (s, [])
  | i :: is, s =>
    match M.exec i s with
    | none => none
    | some s₁ => (execBlock is s₁).map fun p => (p.1, (M.addrs i s).map Leak.addr ++ p.2)

theorem execBlock_append (l₁ l₂ : List M.Instr) (s : M.State) :
    execBlock M (l₁ ++ l₂) s =
      (execBlock M l₁ s).bind fun p =>
        (execBlock M l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    cases M.exec i s with
    | none => rfl
    | some s₁ =>
      simp only [ih]
      cases execBlock M is s₁ with
      | none => rfl
      | some p => simp [Option.map_map, Function.comp_def]

/-- Big-step semantics: terminating, non-faulting executions with their leakage traces. -/
inductive Exec : Prog M → M.State → List Leak → M.State → Prop
  | block {is s s' t} : execBlock M is s = some (s', t) → Exec (.block is) s t s'
  | seq {c₁ c₂ s₁ s₂ s₃ t₁ t₂} :
      Exec c₁ s₁ t₁ s₂ → Exec c₂ s₂ t₂ s₃ → Exec (.seq c₁ c₂) s₁ (t₁ ++ t₂) s₃
  | iteT {c th el s s' t} :
      M.eval c s = some true → Exec th s t s' → Exec (.ite c th el) s (.branch true :: t) s'
  | iteF {c th el s s' t} :
      M.eval c s = some false → Exec el s t s' → Exec (.ite c th el) s (.branch false :: t) s'
  | loopExit {body c s s' t} :
      Exec body s t s' → M.eval c s' = some false →
      Exec (.loop body c) s (t ++ [.branch false]) s'
  | loopNext {body c s s' s'' t t'} :
      Exec body s t s' → M.eval c s' = some true → Exec (.loop body c) s' t' s'' →
      Exec (.loop body c) s (t ++ .branch true :: t') s''

/-- The semantics is deterministic. -/
theorem Exec.det {c : Prog M} {s s₁ s₂ : M.State} {t₁ t₂ : List Leak}
    (h₁ : Exec M c s t₁ s₁) (h₂ : Exec M c s t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing t₂ s₂ with
  | block h => cases h₂ with
    | block h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ => cases h₂ with
    | seq a b =>
      obtain ⟨rfl, rfl⟩ := ih₁ a
      obtain ⟨rfl, rfl⟩ := ih₂ b
      exact ⟨rfl, rfl⟩
  | iteT hc _ ih => cases h₂ with
    | iteT _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
    | iteF hc' _ => rw [hc] at hc'; cases hc'
  | iteF hc _ ih => cases h₂ with
    | iteT hc' _ => rw [hc] at hc'; cases hc'
    | iteF _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
  | loopExit _ hc ih => cases h₂ with
    | loopExit a _ => obtain ⟨rfl, rfl⟩ := ih a; exact ⟨rfl, rfl⟩
    | loopNext a hc' _ =>
      obtain ⟨rfl, rfl⟩ := ih a; rw [hc] at hc'; cases hc'
  | loopNext _ hc _ ih₁ ih₂ => cases h₂ with
    | loopExit a hc' => obtain ⟨rfl, rfl⟩ := ih₁ a; rw [hc] at hc'; cases hc'
    | loopNext a _ b =>
      obtain ⟨rfl, rfl⟩ := ih₁ a
      obtain ⟨rfl, rfl⟩ := ih₂ b
      exact ⟨rfl, rfl⟩

/-! ## Total-correctness weakest preconditions -/

/-- `WP M c s Q`: from `s`, `c` terminates without faulting in a state satisfying `Q`. -/
def WP (c : Prog M) (s : M.State) (Q : M.State → Prop) : Prop :=
  ∃ t s', Exec M c s t s' ∧ Q s'

namespace WP
variable {M}

theorem mono {c : Prog M} {s : M.State} {Q Q' : M.State → Prop}
    (h : WP M c s Q) (hq : ∀ s, Q s → Q' s) : WP M c s Q' := by
  obtain ⟨t, s', he, hq'⟩ := h; exact ⟨t, s', he, hq _ hq'⟩

/-- Straight-line blocks. -/
theorem block {is : List M.Instr} {s : M.State} {Q : M.State → Prop}
    (h : ∃ p, execBlock M is s = some p ∧ Q p.1) : WP M (.block is) s Q := by
  obtain ⟨⟨s', t⟩, h1, h2⟩ := h; exact ⟨t, s', .block h1, h2⟩

theorem block_intro {is : List M.Instr} {s : M.State} {Q : M.State → Prop}
    (p : M.State × List Leak) (h : execBlock M is s = some p) (hq : Q p.1) : WP M (.block is) s Q :=
  ⟨p.2, p.1, .block h, hq⟩

theorem block_append {l₁ l₂ : List M.Instr} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.block l₁) s (fun s₁ => WP M (.block l₂) s₁ Q)) : WP M (.block (l₁ ++ l₂)) s Q := by
  obtain ⟨t, s₁, h1, t', s₂, h2, hq⟩ := h
  cases h1 with | block h1 => cases h2 with | block h2 =>
  exact ⟨_, _, .block (by rw [execBlock_append, h1]; simp [h2]; rfl), hq⟩

theorem block_nil {s : M.State} {Q : M.State → Prop} (h : Q s) : WP M (.block []) s Q :=
  ⟨[], s, .block rfl, h⟩

/-- Iterate a family of straight-line blocks with an indexed invariant. -/
theorem block_iter (f : Nat → List M.Instr) (Inv : Nat → M.State → Prop) (a : Nat) :
    ∀ n, (∀ i < n, ∀ s, Inv (a + i) s → WP M (.block (f (a + i))) s (Inv (a + i + 1))) →
    ∀ s, Inv a s → WP M (.block ((List.range n).map (fun i => f (a + i))).flatten) s (Inv (a + n)) := by
  intro n
  induction n with
  | zero => intro _ s hs; exact block_nil hs
  | succ n ih =>
    intro h s hs
    rw [List.range_succ, List.map_append, List.flatten_append]
    apply block_append
    refine mono (ih (fun i hi => h i (by omega)) s hs) ?_
    intro s₁ h₁
    have := h n (by omega) s₁ h₁
    rw [show a + (n + 1) = a + n + 1 by omega]
    simpa using this

theorem seq {c₁ c₂ : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M c₁ s (fun s₁ => WP M c₂ s₁ Q)) : WP M (.seq c₁ c₂) s Q := by
  obtain ⟨t, s₁, h1, t', s₂, h2, hq⟩ := h; exact ⟨_, _, .seq h1 h2, hq⟩

theorem ite {c : M.Cond} {th el : Prog M} {s : M.State} {Q : M.State → Prop} (b : Bool)
    (hc : M.eval c s = some b) (ht : b = true → WP M th s Q) (he : b = false → WP M el s Q) :
    WP M (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', h1, h2⟩ := he rfl; exact ⟨_, _, .iteF hc h1, h2⟩
  · obtain ⟨t, s', h1, h2⟩ := ht rfl; exact ⟨_, _, .iteT hc h1, h2⟩

/-- The loop rule: an invariant indexed by a natural-number measure that
decreases on every iteration that loops back. -/
theorem loop {body : Prog M} {c : M.Cond} {Q : M.State → Prop}
    (Inv : Nat → M.State → Prop)
    (hstep : ∀ n s, Inv n s → WP M body s (fun s' =>
        (M.eval c s' = some false ∧ Q s') ∨
        (M.eval c s' = some true ∧ ∃ m < n, Inv m s')))
    (n : Nat) (s : M.State) (hs : Inv n s) : WP M (.loop body c) s Q := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    obtain ⟨t, s', h1, h2⟩ := hstep n s hs
    rcases h2 with ⟨hc, hq⟩ | ⟨hc, m, hm, hi⟩
    · exact ⟨_, _, .loopExit h1 hc, hq⟩
    · obtain ⟨t', s'', h3, hq⟩ := ih m hm s' hi
      exact ⟨_, _, .loopNext h1 hc h3, hq⟩

end WP

/-! ## Constant time -/

/-- `c` is constant-time with respect to the relation `Pub` ("the two initial
states agree on all public data") under precondition `Pre`: any two runs from
states that agree on public data produce identical leakage traces. -/
def ConstantTime (Pre : M.State → Prop) (Pub : M.State → M.State → Prop) (c : Prog M) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', Pre s₁ → Pre s₂ → Pub s₁ s₂ →
    Exec M c s₁ t₁ s₁' → Exec M c s₂ t₂ s₂' → t₁ = t₂

end CC
