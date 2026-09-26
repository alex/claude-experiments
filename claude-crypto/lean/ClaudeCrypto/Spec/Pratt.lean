import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime

/-!
# Pratt primality certificates

A generic, proven-sound checker for Pratt certificates, built on Mathlib's
`lucas_primality`.  A certificate is a list of entries `⟨q, a, [(q₁, e₁), …]⟩`
in dependency order: each entry claims that `q` is prime, with Lucas witness
`a` and `q − 1 = ∏ qᵢ ^ eᵢ`, where every `qᵢ` is `2` or the `q` of an earlier
entry.  `checkCert` verifies all of this with a fast modular exponentiation
(`powMod`, binary recursion) so that `decide +kernel` evaluates it using the
kernel's GMP-accelerated `Nat` operations.
-/

namespace CC.Spec.Pratt

/-- `powModAux fuel a e m = a ^ e % m` whenever `e ≤ fuel` (square-and-multiply). -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m
    else
      let r := powModAux fuel (a * a % m) (e / 2) m
      if e % 2 = 0 then r else r * a % m

/-- Modular exponentiation `a ^ e % m`. -/
def powMod (a e m : ℕ) : ℕ := powModAux e a e m

theorem powModAux_eq (fuel a e m : ℕ) (h : e ≤ fuel) : powModAux fuel a e m = a ^ e % m := by
  induction fuel generalizing a e with
  | zero =>
    obtain rfl : e = 0 := by omega
    simp [powModAux]
  | succ k ih =>
    simp only [powModAux]
    split_ifs with h0 h2
    · subst h0; simp
    · rw [ih _ _ (by omega)]
      have key : a ^ e = (a * a) ^ (e / 2) := by rw [← sq, ← pow_mul]; congr 1; omega
      rw [key]
      exact (Nat.mod_modEq (a * a) m).pow _
    · rw [ih _ _ (by omega)]
      have key : a ^ e = (a * a) ^ (e / 2) * a := by
        rw [← sq, ← pow_mul, ← pow_succ]; congr 1; omega
      rw [key]
      exact (((Nat.mod_modEq _ _).trans ((Nat.mod_modEq (a * a) m).pow _)).mul_right a)

theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := powModAux_eq _ _ _ _ le_rfl

/-- One certificate entry: `q` is prime with Lucas witness `a`, and
`q - 1 = ∏ (qᵢ ^ eᵢ)` for `(qᵢ, eᵢ) ∈ fs`. -/
structure Entry where
  q : ℕ
  a : ℕ
  fs : List (ℕ × ℕ)

/-- The checks for one entry, given the list of already-proven primes. -/
def entryOk (known : List ℕ) (e : Entry) : Bool :=
  decide (1 < e.q) && powMod e.a (e.q - 1) e.q == 1 &&
  (e.fs.map (fun f => f.1 ^ f.2)).prod == e.q - 1 &&
  e.fs.all (fun f => (f.1 == 2 || known.contains f.1) && powMod e.a ((e.q - 1) / f.1) e.q != 1)

/-- Check a whole certificate (entries in dependency order). -/
def checkList : List ℕ → List Entry → Bool
  | _, [] => true
  | known, e :: es => entryOk known e && checkList (e.q :: known) es

/-- `checkCert target es`: the certificate is valid and its last entry is `target`. -/
def checkCert (target : ℕ) (es : List Entry) : Bool :=
  checkList [] es && (es.getLast?.map Entry.q == some target)

theorem entryOk_sound (known : List ℕ) (hk : ∀ r ∈ known, r.Prime) (e : Entry)
    (h : entryOk known e = true) : e.q.Prime := by
  simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, hpow⟩, hprod⟩, hall⟩ := h
  rw [powMod_eq] at hpow
  have hq1 : (1 : ℕ) % e.q = 1 := Nat.mod_eq_of_lt h1
  apply lucas_primality e.q (e.a : ZMod e.q)
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, hpow, Nat.cast_one]
  · intro r hr hrd
    rw [← hprod] at hrd
    obtain ⟨x, hx, hrx⟩ := (Prime.dvd_prod_iff hr.prime).1 hrd
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    have hfp : f.1.Prime := by
      rcases (hall f hf).1 with h2 | h2
      · rw [h2]; exact Nat.prime_two
      · exact hk _ h2
    have hrf : r = f.1 := (Nat.prime_dvd_prime_iff_eq hr hfp).1 (hr.dvd_of_dvd_pow hrx)
    subst hrf
    have hne := (hall f hf).2
    rw [powMod_eq] at hne
    rw [← hprod, ← Nat.cast_pow, ← Nat.cast_one, ne_eq, ZMod.natCast_eq_natCast_iff', hq1,
      hprod]
    exact hne

theorem checkList_sound : ∀ (known : List ℕ) (es : List Entry), (∀ r ∈ known, r.Prime) →
    checkList known es = true → ∀ e ∈ es, e.q.Prime
  | _, [], _, _ => by simp
  | known, e :: es, hk, h => by
    simp only [checkList, Bool.and_eq_true] at h
    have he := entryOk_sound known hk e h.1
    have ih := checkList_sound (e.q :: known) es
      (by intro r hr; rcases List.mem_cons.1 hr with rfl | hr; exacts [he, hk r hr]) h.2
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    exacts [he, ih e' he']

theorem checkCert_sound (target : ℕ) (es : List Entry) (h : checkCert target es = true) :
    target.Prime := by
  simp only [checkCert, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hall := checkList_sound [] es (by simp) h1
  cases hl : es.getLast? with
  | none => rw [hl] at h2; simp at h2
  | some e =>
    rw [hl] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    subst h2
    exact hall e (List.mem_of_getLast? hl)

end CC.Spec.Pratt
