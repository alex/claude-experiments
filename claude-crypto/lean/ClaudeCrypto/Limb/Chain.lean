import ClaudeCrypto.Limb.Field

/-! # Limb chains with memory operands: loads, additions and subtractions into `rot 6 ·` -/

namespace CC.Limb

/-- Memory limbs of the 6-limb number at `base + off`. -/
def memX (s : State) (base : Var) (off : Nat) (k : Nat) : Nat :=
  (s.mem.readW (s.r base + BitVec.ofNat 64 (off + 8 * k)) 64).toNat

def ldStep (base : Var) (off : Nat) (k : Nat) : List Instr := [.ld (rot 6 k) base (off + 8 * k)]
def ldRow (base : Var) (off : Nat) : List Instr := ((List.range 6).map fun k => ldStep base off (0 + k)).flatten

/-- `rot 6 k op= mem[base + off + 8k]` with the carry/borrow chain. -/
def arStep (sub : Bool) (base : Var) (off : Nat) (k : Nat) : List Instr :=
  [ .ld 10 base (off + 8 * k),
    match sub, k with
    | false, 0 => .add (rot 6 k) 10
    | false, _ => .adc (rot 6 k) 10
    | true, 0 => .sub (rot 6 k) 10
    | true, _ => .sbb (rot 6 k) 10 ]
def arRow (sub : Bool) (base : Var) (off : Nat) : List Instr :=
  ((List.range 6).map fun k => arStep sub base off (0 + k)).flatten

/-- Everything but `rot 6 ·` and `r10` is unchanged. -/
structure ChainFrame (s0 s : State) : Prop where
  regs : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → s.r v = s0.r v
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels

structure LdInv (base : Var) (off : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  frame : ChainFrame s0 s
  lim : ∀ k < j, (s.r (rot 6 k)).toNat = memX s0 base off k
  cf : s.cf = s0.cf ∧ s.sub = s0.sub

theorem rot6_ne_base (k : Nat) (base : Var) (hb : base.val = 13 ∨ base.val = 14) : rot 6 k ≠ base :=
  rot_ne _ _ _ (by omega)

theorem ldRow_ok (base : Var) (hb : base.val = 13 ∨ base.val = 14) (off : Nat) (s0 : State)
    (hp : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r base + BitVec.ofNat 64 (off + 8 * k)) 8) :
    WP isa (.block (ldRow base off)) s0 (LdInv base off s0 6) := by
  have := WP.block_iter (M := isa) (ldStep base off) (LdInv base off s0) 0 6
    (fun i hi s hs => by
      have rb : s.r base = s0.r base := hs.frame.regs base (fun k _ => (rot6_ne_base k base hb).symm)
        (by intro h; rw [h] at hb; simp at hb)
      have hp' : InRegions (s.rd ++ s.wr) (s.r base + BitVec.ofNat 64 (off + 8 * (0 + i))) 8 := by
        rw [hs.frame.rd, hs.frame.wr, rb]; exact hp _ (by omega)
      refine WP.block_intro _ (ld_exec _ _ _ s hp') ⟨⟨fun v hv h10 => ?_, ?_, ?_, ?_, ?_⟩, fun k hk => ?_, ?_⟩
      · rw [State.set_r, Function.update_of_ne (hv (0 + i) (by omega))]; exact hs.frame.regs v hv h10
      · exact hs.frame.mem
      · exact hs.frame.rd
      · exact hs.frame.wr
      · exact hs.frame.labels
      · simp only [State.set_r]
        rcases Nat.lt_or_ge k (0 + i) with hk' | hk'
        · rw [Function.update_of_ne (rot_ne_rot 6 k (0 + i) (by omega) (by omega) (by omega))]
          exact hs.lim k hk'
        · have : k = 0 + i := by omega
          subst this
          rw [Function.update_self, hs.frame.mem, rb]; rfl
      · exact hs.cf) s0
    ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩, fun k hk => absurd hk (by omega), rfl, rfl⟩
  simpa [ldRow] using this

theorem carry_eq (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat + 2 ^ 64 * (carryOut a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  simp only [carryOut, ble_toNat, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_mod, Nat.reducePow, Nat.one_mod,
    Nat.add_zero] <;> generalize a.toNat = x at * <;> generalize b.toNat = y at * <;> split_ifs <;> omega

/-- The relation established by `j` steps of an add (`sub = false`) or subtract chain. -/
def ArRel (sub : Bool) (t' t X : Nat) (j : Nat) (c : Bool) : Prop :=
  if sub then t' + X = t + 2 ^ (64 * j) * c.toNat else t' + 2 ^ (64 * j) * c.toNat = t + X

structure ArInv (sub : Bool) (base : Var) (off : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  frame : ChainFrame s0 s
  rest : ∀ k, j ≤ k → k < 6 → s.r (rot 6 k) = s0.r (rot 6 k)
  rel : 0 < j → ∃ c, s.cf = some c ∧ s.sub = sub ∧
    ArRel sub (lsum (fun k => (s.r (rot 6 k)).toNat) j) (lsum (fun k => (s0.r (rot 6 k)).toNat) j)
      (lsum (memX s0 base off) j) j c

theorem arStep_ok (sub : Bool) (base : Var) (hb : base.val = 13 ∨ base.val = 14) (off : Nat) (s0 : State)
    (hp : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r base + BitVec.ofNat 64 (off + 8 * k)) 8)
    (j : Nat) (hj : j < 6) (s : State) (h : ArInv sub base off s0 j s) :
    ∃ q, execBlock isa (arStep sub base off j) s = some q ∧ ArInv sub base off s0 (j + 1) q.1 := by
  have b10 : base ≠ 10 := by intro e; rw [e] at hb; simp at hb
  have rb : s.r base = s0.r base := h.frame.regs base (fun k _ => (rot6_ne_base k base hb).symm) b10
  have hp' : InRegions (s.rd ++ s.wr) (s.r base + BitVec.ofNat 64 (off + 8 * j)) 8 := by
    rw [h.frame.rd, h.frame.wr, rb]; exact hp _ hj
  set x := s.mem.readW (s.r base + BitVec.ofNat 64 (off + 8 * j)) 64 with hx
  have hxv : x.toNat = memX s0 base off j := by rw [hx, h.frame.mem, rb]; rfl
  set t := s.r (rot 6 j) with ht
  have htv : t = s0.r (rot 6 j) := h.rest j le_rfl hj
  have n10 : rot 6 j ≠ 10 := rot_ne_10 _ _
  -- the incoming carry
  obtain ⟨c, hc0, hcs, hval⟩ : ∃ c : Bool, (j = 0 → c = false) ∧ (0 < j → s.cf = some c ∧ s.sub = sub) ∧
      ArRel sub (lsum (fun k => (s.r (rot 6 k)).toNat) j) (lsum (fun k => (s0.r (rot 6 k)).toNat) j)
        (lsum (memX s0 base off) j) j c := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact ⟨false, fun _ => rfl, fun h => absurd h (by omega), by cases sub <;> simp [ArRel, lsum]⟩
    · obtain ⟨c, h1, h2, h3⟩ := h.rel h0
      exact ⟨c, fun h => absurd h (by omega), fun _ => ⟨h1, h2⟩, h3⟩
  -- execute: the result register value and the new flag
  obtain ⟨q, hq, qr, qcf, qsub, qm, qrd, qwr, ql⟩ : ∃ q, execBlock isa (arStep sub base off j) s = some q ∧
      q.1.r = Function.update (Function.update s.r 10 x) (rot 6 j)
        (if sub then t - x - (BitVec.ofBool c).setWidth 64 else t + x + (BitVec.ofBool c).setWidth 64) ∧
      q.1.cf = some (if sub then borrowOut t x c else carryOut t x c) ∧ q.1.sub = sub ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · have hc := hc0 h0
      subst h0 hc
      cases sub <;> simp only [arStep] <;> limb_sym [hp', n10] <;> refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp [ht, hx]
    · obtain ⟨hcf, hsub⟩ := hcs h0
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      subst hsub
      cases h' : s.sub <;> simp only [arStep] <;> limb_sym [hp', n10, hcf, h'] <;>
        refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;> simp [ht, hx]
  refine ⟨q, hq, ⟨fun v hv h10 => ?_, qm.trans h.frame.mem, qrd.trans h.frame.rd, qwr.trans h.frame.wr,
    ql.trans h.frame.labels⟩, fun k hk1 hk2 => ?_, fun _ => ⟨_, qcf, qsub, ?_⟩⟩
  · rw [qr, Function.update_of_ne (hv j hj), Function.update_of_ne h10]
    exact h.frame.regs v hv h10
  · rw [qr, Function.update_of_ne (rot_ne_rot 6 k j (by omega) (by omega) (by omega)),
      Function.update_of_ne (rot_ne_10 _ _)]
    exact h.rest k (by omega) hk2
  · have hl : lsum (fun k => (q.1.r (rot 6 k)).toNat) j = lsum (fun k => (s.r (rot 6 k)).toNat) j := by
      apply lsum_congr; intro k hk
      rw [qr, Function.update_of_ne (rot_ne_rot 6 k j (by omega) (by omega) (by omega)),
        Function.update_of_ne (rot_ne_10 _ _)]
    have hj' : (q.1.r (rot 6 j)) = (if sub then t - x - (BitVec.ofBool c).setWidth 64
        else t + x + (BitVec.ofBool c).setWidth 64) := by rw [qr, Function.update_self]
    unfold ArRel at hval ⊢
    rw [lsum_succ, lsum_succ, lsum_succ, hl, hj', ← htv, ← hxv,
      show 64 * (j + 1) = 64 * j + 64 by ring, pow_add]
    cases sub
    · have ce := carry_eq t x c
      simp only [Bool.false_eq_true, ite_false] at hval ⊢
      zify at hval ce ⊢
      linear_combination hval + (2 : ℤ) ^ (64 * j) * ce
    · have be := borrow_eq t x c
      simp only [ite_true] at hval ⊢
      zify at hval be ⊢
      linear_combination hval + (2 : ℤ) ^ (64 * j) * be

theorem arRow_ok (sub : Bool) (base : Var) (hb : base.val = 13 ∨ base.val = 14) (off : Nat) (s0 : State)
    (hp : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r base + BitVec.ofNat 64 (off + 8 * k)) 8) :
    WP isa (.block (arRow sub base off)) s0 (ArInv sub base off s0 6) := by
  have := WP.block_iter (M := isa) (arStep sub base off) (ArInv sub base off s0) 0 6
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := arStep_ok sub base hb off s0 hp (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') s0
    ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩, fun _ _ _ => rfl, fun h => absurd h (by omega)⟩
  simpa [arRow] using this

end CC.Limb
