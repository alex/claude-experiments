import ClaudeCrypto.Framework.Code

/-!
# Constant-time verification by taint analysis

A *taint domain* for an ISA abstracts "which parts of the machine state are
public".  `Agree t s₁ s₂` says that `s₁` and `s₂` agree on everything `t`
marks public.  The abstract `step` must be sound: if two states agree on the
public part, a step either is rejected by the analysis (`none`), or it
accesses the same addresses in both states and the resulting states agree on
the public part of the new abstract state.

`analyze` runs the abstract interpreter over structured code (computing a
fixpoint for loops).  `analyze_sound` then shows: if `analyze c t = some t'`,
any two executions of `c` from `t`-agreeing states produce *identical
leakage traces* (control flow and memory addresses).

Since `analyze` is an executable function, checking a concrete program is a
matter of evaluation (`decide`).
-/

namespace CC

structure TaintDom (M : ISA) where
  T : Type
  step : M.Instr → T → Option T
  condOk : M.Cond → T → Bool
  join : T → T → T
  /-- `le a b`: everything public in `b` is public in `a` (so `Agree a → Agree b`). -/
  le : T → T → Bool
  Agree : T → M.State → M.State → Prop
  step_sound : ∀ i t t' s₁ s₂ s₁' s₂', step i t = some t' → Agree t s₁ s₂ →
    M.exec i s₁ = some s₁' → M.exec i s₂ = some s₂' → M.addrs i s₁ = M.addrs i s₂ ∧ Agree t' s₁' s₂'
  cond_sound : ∀ c t s₁ s₂, condOk c t = true → Agree t s₁ s₂ → M.eval c s₁ = M.eval c s₂
  le_sound : ∀ a b s₁ s₂, le a b = true → Agree a s₁ s₂ → Agree b s₁ s₂
  le_refl : ∀ a, le a a = true
  le_join_left : ∀ a b, le a (join a b) = true
  le_join_right : ∀ a b, le b (join a b) = true

namespace TaintDom

variable {M : ISA} (D : TaintDom M)

def analyzeBlock : List M.Instr → D.T → Option D.T
  | [], t => some t
  | i :: is, t => (D.step i t).bind (analyzeBlock is)

/-- Loop fixpoint iteration: `x ↦ join x (f x)` until `f x ≤ x`. -/
def loopIter (f : D.T → Option D.T) (ok : D.T → Bool) : Nat → D.T → Option D.T
  | 0, _ => none
  | n + 1, x =>
    match f x with
    | none => none
    | some tb => if D.le tb x && ok tb then some x else loopIter f ok n (D.join x tb)

/-- Abstract interpretation of structured code.  Loops iterate
`t ↦ join t (body t)` at most `fuel` times looking for a post-fixpoint. -/
def analyze (fuel : Nat) : Code M.Instr M.Cond → D.T → Option D.T
  | .block is, t => D.analyzeBlock is t
  | .seq c₁ c₂, t => (analyze fuel c₁ t).bind (analyze fuel c₂)
  | .ite c th el, t =>
    if D.condOk c t then
      (analyze fuel th t).bind fun a => (analyze fuel el t).map fun b => D.join a b
    else none
  | .loop body c, t => D.loopIter (analyze fuel body) (D.condOk c) fuel t

theorem analyzeBlock_sound (is : List M.Instr) : ∀ t t' s₁ s₂ s₁' s₂' tr₁ tr₂,
    D.analyzeBlock is t = some t' → D.Agree t s₁ s₂ →
    execBlock M is s₁ = some (s₁', tr₁) → execBlock M is s₂ = some (s₂', tr₂) →
    tr₁ = tr₂ ∧ D.Agree t' s₁' s₂' := by
  induction is with
  | nil =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    simp only [analyzeBlock, Option.some.injEq] at ha
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2; subst ha
    exact ⟨rfl, hag⟩
  | cons i is ih =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    simp only [analyzeBlock] at ha
    cases hs : D.step i t with
    | none => rw [hs] at ha; cases ha
    | some t₁ =>
      rw [hs, Option.bind_some] at ha
      simp only [execBlock] at h1 h2
      cases he1 : M.exec i s₁ with
      | none => simp [he1] at h1
      | some u₁ =>
        cases he2 : M.exec i s₂ with
        | none => simp [he2] at h2
        | some u₂ =>
          simp only [he1] at h1; simp only [he2] at h2
          obtain ⟨haddr, hag₁⟩ := D.step_sound i t t₁ s₁ s₂ u₁ u₂ hs hag he1 he2
          cases hb1 : execBlock M is u₁ with
          | none => simp [hb1] at h1
          | some p₁ =>
            cases hb2 : execBlock M is u₂ with
            | none => simp [hb2] at h2
            | some p₂ =>
              simp only [hb1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
              simp only [hb2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
              obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
              obtain ⟨htr, hag'⟩ := ih t₁ t' u₁ u₂ p₁.1 p₂.1 p₁.2 p₂.2 ha hag₁ hb1 hb2
              exact ⟨by rw [haddr, htr], hag'⟩

/-- Soundness of loop invariants: if `tinv` is a post-fixpoint of the body,
the whole loop leaks the same trace from `tinv`-agreeing states. -/
theorem loop_sound (fuel : Nat) (body : Code M.Instr M.Cond) (c : M.Cond) (tinv tb : D.T)
    (hbody : D.analyze fuel body tinv = some tb) (hle : D.le tb tinv = true) (hc : D.condOk c tb = true)
    (ih : ∀ t t' s₁ s₂ s₁' s₂' tr₁ tr₂, D.analyze fuel body t = some t' → D.Agree t s₁ s₂ →
      Exec M body s₁ tr₁ s₁' → Exec M body s₂ tr₂ s₂' → tr₁ = tr₂ ∧ D.Agree t' s₁' s₂') :
    ∀ s₁ s₂ s₁' s₂' tr₁ tr₂, D.Agree tinv s₁ s₂ →
      Exec M (.loop body c) s₁ tr₁ s₁' → Exec M (.loop body c) s₂ tr₂ s₂' →
      tr₁ = tr₂ ∧ D.Agree tinv s₁' s₂' := by
  intro s₁ s₂ s₁' s₂' tr₁ tr₂ hag h1 h2
  generalize hc₁ : Code.loop body c = cl at h1
  induction h1 generalizing s₂ tr₂ s₂' with
  | loopExit hb1 hc1 =>
    cases hc₁
    cases h2 with
    | loopExit hb2 hc2 =>
      obtain ⟨htr, hag'⟩ := ih _ _ _ _ _ _ _ _ hbody hag hb1 hb2
      exact ⟨by rw [htr], D.le_sound _ _ _ _ hle hag'⟩
    | loopNext hb2 hc2 _ =>
      obtain ⟨_, hag'⟩ := ih _ _ _ _ _ _ _ _ hbody hag hb1 hb2
      have := D.cond_sound _ _ _ _ hc hag'
      rw [hc1, hc2] at this; cases this
  | loopNext hb1 hc1 _ _ ih₂ =>
    cases hc₁
    cases h2 with
    | loopExit hb2 hc2 =>
      obtain ⟨_, hag'⟩ := ih _ _ _ _ _ _ _ _ hbody hag hb1 hb2
      have := D.cond_sound _ _ _ _ hc hag'
      rw [hc1, hc2] at this; cases this
    | loopNext hb2 hc2 hl2 =>
      obtain ⟨htr, hag'⟩ := ih _ _ _ _ _ _ _ _ hbody hag hb1 hb2
      obtain ⟨htr', hag''⟩ := ih₂ _ _ _ (D.le_sound _ _ _ _ hle hag') hl2 rfl
      exact ⟨by rw [htr, htr'], hag''⟩
  | _ => cases hc₁

theorem loopFix_spec (fuel : Nat) (body : Code M.Instr M.Cond) (c : M.Cond) :
    ∀ n x t', D.loopIter (D.analyze fuel body) (D.condOk c) n x = some t' →
      (∀ s₁ s₂, D.Agree x s₁ s₂ → D.Agree t' s₁ s₂) ∧ ∃ tb, D.analyze fuel body t' = some tb ∧
        D.le tb t' = true ∧ D.condOk c tb = true := by
  intro n
  induction n with
  | zero => intro x t' h; simp [loopIter] at h
  | succ n ih =>
    intro x t' h
    simp only [loopIter] at h
    split at h
    · cases h
    · rename_i tb hb
      split at h
      · rename_i hcond
        cases h
        simp only [Bool.and_eq_true] at hcond
        exact ⟨fun _ _ h => h, tb, hb, hcond.1, hcond.2⟩
      · obtain ⟨hle, rest⟩ := ih _ _ h
        exact ⟨fun s₁ s₂ hs => hle _ _ (D.le_sound _ _ _ _ (D.le_join_left _ _) hs), rest⟩

/-- **Soundness of the taint analysis**: equal leakage for executions from
states that agree on the public data. -/
theorem analyze_sound (fuel : Nat) (c : Code M.Instr M.Cond) :
    ∀ t t' s₁ s₂ s₁' s₂' tr₁ tr₂, D.analyze fuel c t = some t' → D.Agree t s₁ s₂ →
      Exec M c s₁ tr₁ s₁' → Exec M c s₂ tr₂ s₂' → tr₁ = tr₂ ∧ D.Agree t' s₁' s₂' := by
  induction c with
  | block is =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    cases h1 with | block h1 => cases h2 with | block h2 =>
    exact D.analyzeBlock_sound is t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
  | seq c₁ c₂ ih₁ ih₂ =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    simp only [analyze] at ha
    cases ha1 : D.analyze fuel c₁ t with
    | none => rw [ha1] at ha; cases ha
    | some t₁ =>
      rw [ha1, Option.bind_some] at ha
      cases h1 with | seq a1 b1 => cases h2 with | seq a2 b2 =>
      obtain ⟨e1, g1⟩ := ih₁ _ _ _ _ _ _ _ _ ha1 hag a1 a2
      obtain ⟨e2, g2⟩ := ih₂ _ _ _ _ _ _ _ _ ha g1 b1 b2
      exact ⟨by rw [e1, e2], g2⟩
  | ite c th el ih₁ ih₂ =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    simp only [analyze] at ha
    split at ha
    · rename_i hc
      have hcs := D.cond_sound _ _ _ _ hc hag
      cases hth : D.analyze fuel th t with
      | none => rw [hth] at ha; cases ha
      | some a =>
        cases hel : D.analyze fuel el t with
        | none => rw [hth, hel] at ha; cases ha
        | some b =>
          rw [hth, hel] at ha
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at ha
          subst ha
          cases h1 with
          | iteT c1 x1 =>
            cases h2 with
            | iteT c2 x2 =>
              obtain ⟨e, g⟩ := ih₁ _ _ _ _ _ _ _ _ hth hag x1 x2
              exact ⟨by rw [e], D.le_sound _ _ _ _ (D.le_join_left _ _) g⟩
            | iteF c2 _ => rw [c1, c2] at hcs; cases hcs
          | iteF c1 x1 =>
            cases h2 with
            | iteT c2 _ => rw [c1, c2] at hcs; cases hcs
            | iteF c2 x2 =>
              obtain ⟨e, g⟩ := ih₂ _ _ _ _ _ _ _ _ hel hag x1 x2
              exact ⟨by rw [e], D.le_sound _ _ _ _ (D.le_join_right _ _) g⟩
    · cases ha
  | loop body c ih =>
    intro t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ha hag h1 h2
    simp only [analyze] at ha
    obtain ⟨hinit, tb, hb, hle, hc⟩ := D.loopFix_spec fuel body c _ _ _ ha
    exact D.loop_sound fuel body c t' tb hb hle hc ih _ _ _ _ _ _ (hinit _ _ hag) h1 h2

/-- A program accepted by the analysis is constant-time. -/
theorem constantTime_of_analyze (fuel : Nat) (c : Code M.Instr M.Cond) (t : D.T)
    (h : (D.analyze fuel c t).isSome = true) (Pre : M.State → Prop) :
    ConstantTime M Pre (D.Agree t) c := by
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' _ _ hag h1 h2
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp h
  exact (D.analyze_sound fuel c t t' s₁ s₂ s₁' s₂' tr₁ tr₂ ht' hag h1 h2).1

end TaintDom
end CC
