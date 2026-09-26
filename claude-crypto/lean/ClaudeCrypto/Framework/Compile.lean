import ClaudeCrypto.Framework.Code

/-!
# Compiling structured code between instruction sets

A `Compiler A B` maps each instruction of `A` to a block of `B` instructions,
and each branch condition of `A` to a block of `B` instructions (e.g. a
`test`) followed by a `B` condition.  `Compiler.code` lifts this to structured
programs.

`Compiler.simulation` shows: if every instruction and every condition is
simulated with respect to a relation `R` between states, then every
terminating, non-faulting execution of an `A` program is simulated by one of
the compiled `B` program.  So properties proven about an `A` program (the
limb-level IR) transfer to the machine code for `B` (an actual architecture),
and only the per-instruction simulation has to be proven for each
architecture.
-/

namespace CC

variable {A B : ISA}

structure Compiler (A B : ISA) where
  instr : A.Instr → List B.Instr
  cond : A.Cond → List B.Instr × B.Cond

namespace Compiler

variable (C : Compiler A B)

def code : Code A.Instr A.Cond → Code B.Instr B.Cond
  | .block is => .block (is.flatMap C.instr)
  | .seq c₁ c₂ => .seq (code c₁) (code c₂)
  | .ite c t e => .seq (.block (C.cond c).1) (.ite (C.cond c).2 (code t) (code e))
  | .loop body c => .loop (.seq (code body) (.block (C.cond c).1)) (C.cond c).2

/-- The simulation obligations. -/
structure Sim (R : A.State → B.State → Prop) : Prop where
  instr : ∀ i s s' t, R s t → A.exec i s = some s' →
    ∃ q, execBlock B (C.instr i) t = some q ∧ R s' q.1
  cond : ∀ c s t b, R s t → A.eval c s = some b →
    ∃ q, execBlock B (C.cond c).1 t = some q ∧ R s q.1 ∧ B.eval (C.cond c).2 q.1 = some b

variable {C} {R : A.State → B.State → Prop}

theorem Sim.block (h : C.Sim R) (is : List A.Instr) :
    ∀ s s' t tr, R s t → execBlock A is s = some (s', tr) →
      ∃ q, execBlock B (is.flatMap C.instr) t = some q ∧ R s' q.1 := by
  induction is with
  | nil =>
    intro s s' t tr hr he
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact ⟨(t, []), rfl, hr⟩
  | cons i is ih =>
    intro s s' t tr hr he
    simp only [execBlock] at he
    cases h1 : A.exec i s with
    | none => rw [h1] at he; cases he
    | some s₁ =>
      rw [h1] at he
      simp only at he
      cases h2 : execBlock A is s₁ with
      | none => rw [h2] at he; cases he
      | some p =>
        rw [h2] at he
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        obtain ⟨q₁, hq₁, hr₁⟩ := h.instr i s s₁ t hr h1
        obtain ⟨q₂, hq₂, hr₂⟩ := ih s₁ p.1 q₁.1 p.2 hr₁ (by rw [h2])
        refine ⟨(q₂.1, q₁.2 ++ q₂.2), ?_, hr₂⟩
        rw [List.flatMap_cons, execBlock_append, hq₁, Option.bind_some, hq₂, Option.map_some]

theorem Sim.exec (h : C.Sim R) {c : Code A.Instr A.Cond} {s s' : A.State} {tr : List Leak}
    (he : Exec A c s tr s') : ∀ t, R s t → ∃ tr' t', Exec B (C.code c) t tr' t' ∧ R s' t' := by
  induction he with
  | block hb =>
    intro t hr
    obtain ⟨q, hq, hr'⟩ := h.block _ _ _ t _ hr hb
    exact ⟨q.2, q.1, .block hq, hr'⟩
  | seq _ _ ih₁ ih₂ =>
    intro t hr
    obtain ⟨tr₁, t₁, e₁, r₁⟩ := ih₁ t hr
    obtain ⟨tr₂, t₂, e₂, r₂⟩ := ih₂ t₁ r₁
    exact ⟨_, _, .seq e₁ e₂, r₂⟩
  | iteT hc _ ih =>
    intro t hr
    obtain ⟨q, hq, hr', hc'⟩ := h.cond _ _ t _ hr hc
    obtain ⟨tr₁, t₁, e₁, r₁⟩ := ih q.1 hr'
    exact ⟨_, _, .seq (.block hq) (.iteT hc' e₁), r₁⟩
  | iteF hc _ ih =>
    intro t hr
    obtain ⟨q, hq, hr', hc'⟩ := h.cond _ _ t _ hr hc
    obtain ⟨tr₁, t₁, e₁, r₁⟩ := ih q.1 hr'
    exact ⟨_, _, .seq (.block hq) (.iteF hc' e₁), r₁⟩
  | loopExit _ hc ih =>
    intro t hr
    obtain ⟨tr₁, t₁, e₁, r₁⟩ := ih t hr
    obtain ⟨q, hq, hr', hc'⟩ := h.cond _ _ t₁ _ r₁ hc
    exact ⟨_, _, .loopExit (.seq e₁ (.block hq)) hc', hr'⟩
  | loopNext _ hc _ ih₁ ih₂ =>
    intro t hr
    obtain ⟨tr₁, t₁, e₁, r₁⟩ := ih₁ t hr
    obtain ⟨q, hq, hr', hc'⟩ := h.cond _ _ t₁ _ r₁ hc
    obtain ⟨tr₂, t₂, e₂, r₂⟩ := ih₂ q.1 hr'
    exact ⟨_, _, .loopNext (.seq e₁ (.block hq)) hc' e₂, r₂⟩

/-- Weakest preconditions transfer along a simulation. -/
theorem Sim.wp (h : C.Sim R) {c : Code A.Instr A.Cond} {s : A.State} {Q : A.State → Prop}
    (hw : WP A c s Q) (t : B.State) (hr : R s t) :
    WP B (C.code c) t (fun t' => ∃ s', R s' t' ∧ Q s') := by
  obtain ⟨tr, s', he, hq⟩ := hw
  obtain ⟨tr', t', e', r'⟩ := h.exec he t hr
  exact ⟨tr', t', e', s', r', hq⟩

end Compiler

end CC
