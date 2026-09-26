import ClaudeCrypto.Limb.Mac

/-! # A row of multiply-accumulates: `t[0..n) += r0 * x[0..n)` with a carry word -/

namespace CC.Limb

/-- Little-endian value of `n` limbs `f 0, f 1, …` (base `2^64`). -/
def lsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => lsum f j + f j * 2 ^ (64 * j)

theorem lsum_succ (f : Nat → Nat) (j : Nat) : lsum f (j + 1) = lsum f j + f j * 2 ^ (64 * j) := rfl

theorem lsum_congr (f g : Nat → Nat) (j : Nat) (h : ∀ k < j, f k = g k) : lsum f j = lsum g j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [lsum_succ, lsum_succ, ih (fun k hk => h k (by omega)), h j (by omega)]

/-- Carry-in register of step `j` (zero register for the first step). -/
def cin (z cA cB : Var) (j : Nat) : Var := if j = 0 then z else if j % 2 = 1 then cA else cB
/-- Carry-out register of step `j` (it first receives the loaded factor). -/
def cout (cA cB : Var) (j : Nat) : Var := if j % 2 = 0 then cA else cB

theorem cin_succ (z cA cB : Var) (j : Nat) : cin z cA cB (j + 1) = cout cA cB j := by
  simp only [cin, cout, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
  split_ifs <;> first | rfl | omega

def macStep (tr : Nat → Var) (base : Var) (off : Nat → Nat) (cA cB lo z : Var) (j : Nat) : List Instr :=
  .ld (cout cA cB j) base (off j) :: mac2 (tr j) (cin z cA cB j) (cout cA cB j) lo z

/-- `t[k] += r0 * mem[base + off k]` for `k < n`, carry word into `cin (n)`. -/
def macRow (tr : Nat → Var) (base : Var) (off : Nat → Nat) (cA cB lo z : Var) (n : Nat) : List Instr :=
  ((List.range n).map fun j => macStep tr base off cA cB lo z (0 + j)).flatten

/-- Register-allocation conditions for a row. -/
structure RowRegs (tr : Nat → Var) (base cA cB lo z : Var) (n : Nat) : Prop where
  inj : ∀ i < n, ∀ j < n, tr i = tr j → i = j
  t_ne : ∀ j < n, tr j ≠ 0 ∧ tr j ≠ cA ∧ tr j ≠ cB ∧ tr j ≠ lo ∧ tr j ≠ z ∧ tr j ≠ base
  cA_cB : cA ≠ cB
  cA_ne : cA ≠ 0 ∧ cA ≠ lo ∧ cA ≠ z ∧ cA ≠ base
  cB_ne : cB ≠ 0 ∧ cB ≠ lo ∧ cB ≠ z ∧ cB ≠ base
  lo_ne : lo ≠ 0 ∧ lo ≠ z ∧ lo ≠ base

/-- The loaded factors. -/
def rowX (s : State) (base : Var) (off : Nat → Nat) (k : Nat) : Nat :=
  (s.mem.readW (s.r base + BitVec.ofNat 64 (off k)) 64).toNat

structure RowInv (tr : Nat → Var) (base : Var) (off : Nat → Nat) (cA cB lo z : Var) (s0 : State)
    (j : Nat) (s : State) : Prop where
  val : lsum (fun k => (s.r (tr k)).toNat) j + 2 ^ (64 * j) * (s.r (cin z cA cB j)).toNat =
    lsum (fun k => (s0.r (tr k)).toNat) j + (s0.r 0).toNat * lsum (rowX s0 base off) j
  frame : ∀ v, (∀ k < j, v ≠ tr k) → v ≠ cA → v ≠ cB → v ≠ lo → s.r v = s0.r v
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels

theorem macStep_ok (tr : Nat → Var) (base : Var) (off : Nat → Nat) (cA cB lo z : Var) (n : Nat)
    (hr : RowRegs tr base cA cB lo z n) (s0 : State) (hz : s0.r z = 0)
    (hp : ∀ k < n, InRegions (s0.rd ++ s0.wr) (s0.r base + BitVec.ofNat 64 (off k)) 8)
    (j : Nat) (hj : j < n) (s : State) (h : RowInv tr base off cA cB lo z s0 j s) :
    ∃ q, execBlock isa (macStep tr base off cA cB lo z j) s = some q ∧
      RowInv tr base off cA cB lo z s0 (j + 1) q.1 := by
  obtain ⟨t0, tA, tB, tl, tz, tb⟩ := hr.t_ne j hj
  have hbase : s.r base = s0.r base := h.frame base (fun k hk => (hr.t_ne k (by omega)).2.2.2.2.2.symm)
    hr.cA_ne.2.2.2.symm hr.cB_ne.2.2.2.symm hr.lo_ne.2.2.symm
  have hzs : s.r z = 0 := by
    rw [h.frame z (fun k hk => (hr.t_ne k (by omega)).2.2.2.2.1.symm) hr.cA_ne.2.2.1.symm hr.cB_ne.2.2.1.symm
      hr.lo_ne.2.1.symm, hz]
  have h0 : s.r 0 = s0.r 0 := h.frame 0 (fun k hk => (hr.t_ne k (by omega)).1.symm) hr.cA_ne.1.symm
    hr.cB_ne.1.symm hr.lo_ne.1.symm
  obtain ⟨a0, al, az, ab⟩ := hr.cA_ne
  obtain ⟨b0, bl, bz, bb⟩ := hr.cB_ne
  have ab' := hr.cA_cB
  have hcout : cout cA cB j ≠ cin z cA cB j ∧ cout cA cB j ≠ 0 ∧ cout cA cB j ≠ lo ∧ cout cA cB j ≠ z ∧
      tr j ≠ cout cA cB j := by
    simp only [cout, cin]
    split_ifs <;> first
      | (exfalso; omega)
      | exact ⟨az, a0, al, az, tA⟩
      | exact ⟨ab', a0, al, az, tA⟩
      | exact ⟨Ne.symm ab', b0, bl, bz, tB⟩
  have hcin : tr j ≠ cin z cA cB j ∧ cin z cA cB j ≠ lo := by
    simp only [cin]
    split_ifs
    · exact ⟨tz, hr.lo_ne.2.1.symm⟩
    · exact ⟨tA, al⟩
    · exact ⟨tB, bl⟩
  -- the load
  have hload : s.load (s.r base + BitVec.ofNat 64 (off j)) =
      some (s0.mem.readW (s0.r base + BitVec.ofNat 64 (off j)) 64) := by
    simp only [State.load, hbase, h.rd, h.wr, h.mem, hp j hj, ite_true]
  set s1 := s.set (cout cA cB j) (s0.mem.readW (s0.r base + BitVec.ofNat 64 (off j)) 64) with hs1
  have e1 : isa.exec (.ld (cout cA cB j) base (off j)) s = some s1 := by
    simp only [isa, CC.Limb.exec, hload, Option.map_some]
    rw [hs1]
  obtain ⟨q, hq, hval, hfr, -, -, hm, hrd, hwr, hl⟩ :=
    mac2_exec (tr j) (cin z cA cB j) (cout cA cB j) lo z s1 hcin.1 hcout.2.2.2.2 tl tz hcout.1.symm hcin.2
      hcout.2.2.1 hcout.2.2.2.1 hr.lo_ne.2.1 hr.lo_ne.1 hcout.2.1 t0
      (by rw [hs1, State.set_r, Function.update_of_ne (Ne.symm hcout.2.2.2.1)]; exact hzs)
  refine ⟨(q.1, (addrs (.ld (cout cA cB j) base (off j)) s).map Leak.addr ++ q.2), ?_, ?_⟩
  · rw [macStep, execBlock, e1]
    simp only [hq, Option.map_some]
  have hcA : cout cA cB j = cA ∨ cout cA cB j = cB := by simp only [cout]; split_ifs <;> simp
  have hq1 : ∀ v, v ≠ tr j → v ≠ cout cA cB j → v ≠ lo → q.1.r v = s.r v := by
    intro v h1 h2 h3
    rw [hfr v h1 h2 h3, hs1, State.set_r, Function.update_of_ne h2]
  have hsj : s.r (tr j) = s0.r (tr j) :=
    h.frame _ (fun k hk he => absurd (hr.inj j hj k (by omega) he) (by omega)) tA tB tl
  have hs1j : s1.r (tr j) = s.r (tr j) := by rw [hs1, State.set_r, Function.update_of_ne hcout.2.2.2.2]
  have hs10 : s1.r 0 = s0.r 0 := by rw [hs1, State.set_r, Function.update_of_ne (Ne.symm hcout.2.1), h0]
  have hs1c : s1.r (cout cA cB j) = s0.mem.readW (s0.r base + BitVec.ofNat 64 (off j)) 64 := by
    rw [hs1, State.set_r, Function.update_self]
  have hs1i : s1.r (cin z cA cB j) = s.r (cin z cA cB j) := by
    rw [hs1, State.set_r, Function.update_of_ne hcout.1.symm]
  refine ⟨?_, ?_, by rw [hm, hs1]; exact h.mem, by rw [hrd, hs1]; exact h.rd, by rw [hwr, hs1]; exact h.wr,
    by rw [hl, hs1]; exact h.labels⟩
  · rw [cin_succ, lsum_succ, lsum_succ, lsum_succ]
    have hl : lsum (fun k => (q.1.r (tr k)).toNat) j = lsum (fun k => (s.r (tr k)).toNat) j := by
      apply lsum_congr
      intro k hk
      have hne : tr k ≠ tr j := fun he => absurd (hr.inj k (by omega) j hj he) (by omega)
      have := hr.t_ne k (by omega)
      rw [hq1 _ hne (by rcases hcA with h' | h' <;> rw [h'] <;> simp_all) this.2.2.2.1]
    rw [hl]
    have hv := h.val
    rw [hs1j, hs10, hs1c, hs1i, hsj] at hval
    simp only [rowX] at hv ⊢
    rw [show 64 * (j + 1) = 64 * j + 64 by ring, pow_add]
    zify at hv hval ⊢
    linear_combination hv + (2 : ℤ) ^ (64 * j) * hval
  · intro v hv h2 h3 h4
    have hvj : v ≠ tr j := hv j (by omega)
    have hvc : v ≠ cout cA cB j := by rcases hcA with h' | h' <;> rw [h'] <;> assumption
    rw [hq1 v hvj hvc h4]
    exact h.frame v (fun k hk => hv k (by omega)) h2 h3 h4

theorem macRow_ok (tr : Nat → Var) (base : Var) (off : Nat → Nat) (cA cB lo z : Var) (n : Nat)
    (hr : RowRegs tr base cA cB lo z n) (s0 : State) (hz : s0.r z = 0)
    (hp : ∀ k < n, InRegions (s0.rd ++ s0.wr) (s0.r base + BitVec.ofNat 64 (off k)) 8) :
    WP isa (.block (macRow tr base off cA cB lo z n)) s0 (RowInv tr base off cA cB lo z s0 n) := by
  have := WP.block_iter (M := isa) (macStep tr base off cA cB lo z) (RowInv tr base off cA cB lo z s0) 0 n
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := macStep_ok tr base off cA cB lo z n hr s0 hz hp (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') s0
    ⟨by simp [lsum, cin, hz], fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  simpa [macRow] using this

theorem lsum_shift (f : Nat → Nat) (n : Nat) :
    lsum f (n + 1) = f 0 + 2 ^ 64 * lsum (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [lsum]
  | succ n ih =>
    rw [lsum_succ, ih, lsum_succ]
    rw [show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]; ring

theorem lsum_lt (f : Nat → Nat) (n : Nat) (h : ∀ k < n, f k < 2 ^ 64) : lsum f n < 2 ^ (64 * n) := by
  induction n with
  | zero => simp [lsum]
  | succ n ih =>
    rw [lsum_succ, show 64 * (n + 1) = 64 * n + 64 by ring, pow_add]
    have := ih (fun k hk => h k (by omega))
    have := h n (by omega)
    nlinarith [pow_pos (show (0 : ℕ) < 2 by norm_num) (64 * n)]

theorem lsum_mod (f : Nat → Nat) (n x : Nat) (hf : f 0 < 2 ^ 64) :
    (lsum f (n + 1) + 2 ^ (64 * (n + 1)) * x) % 2 ^ 64 = f 0 := by
  rw [lsum_shift, show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]
  rw [show f 0 + 2 ^ 64 * lsum (fun k => f (k + 1)) n + 2 ^ 64 * 2 ^ (64 * n) * x =
    f 0 + 2 ^ 64 * (lsum (fun k => f (k + 1)) n + 2 ^ (64 * n) * x) by ring]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]

end CC.Limb
