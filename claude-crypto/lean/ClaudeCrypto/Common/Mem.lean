import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Byte-addressed memory

Memory is a total function from 64-bit addresses to bytes.  Multi-byte
accesses are little-endian (all three supported targets run little-endian).

Memory *safety* is not a property of `Mem` itself: each machine state also
carries the list of regions the code is allowed to read and write, and every
load/store in the instruction semantics faults (returns `none`) if it touches
a byte outside of those regions.  Proving that a program runs to completion
therefore proves it only ever touches permitted memory.
-/

namespace CC

abbrev Addr := BitVec 64
abbrev Byte := BitVec 8
abbrev Mem := Addr → Byte

namespace Mem

/-- Little-endian read of `n` bytes starting at `a` (addresses wrap mod 2^64). -/
def read (m : Mem) (a : Addr) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 => (read m (a + 1) n ++ m a : BitVec (8 * n + 8))

/-- Little-endian read of a `w`-bit value (`w` a multiple of 8). -/
def readW (m : Mem) (a : Addr) (w : Nat) : BitVec w := (m.read a (w / 8)).setWidth w

/-- Little-endian write of the `n`-byte value `v` starting at `a`. -/
def write (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Mem :=
  fun x => if (x - a).toNat < n then v.extractLsb' (8 * (x - a).toNat) 8 else m x

theorem getLsbD_read (m : Mem) (a : Addr) (n i : Nat) :
    (m.read a n).getLsbD i =
      (decide (i < 8 * n) && (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)) := by
  induction n generalizing a i with
  | zero => simp [read]
  | succ n ih =>
    simp only [read, BitVec.getLsbD_append, ih]
    by_cases h : i < 8
    · simp only [h, ite_true]
      have : i / 8 = 0 := by omega
      have h2 : i % 8 = i := by omega
      simp [this, h2]
      intro; omega
    · simp only [h, ite_false]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      have e3 : a + 1 + BitVec.ofNat 64 (i / 8 - 1) = a + BitVec.ofNat 64 (i / 8) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        have h1 : (1 : BitVec 64).toNat = 1 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
        omega
      rw [e3]
      congr 1
      simp only [decide_eq_decide]; omega

theorem toNat_sub_add_ofNat (a : Addr) (k : Nat) (hk : k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k - a).toNat = k := by
  rw [show a + BitVec.ofNat 64 k - a = BitVec.ofNat 64 k by abel, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk

theorem write_apply (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr) :
    m.write a n v x =
      if (x - a).toNat < n then v.extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

/-- Reading back exactly what was written. -/
@[simp] theorem read_write_same (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n))
    (hn : n ≤ 2 ^ 64) : (m.write a n v).read a n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read, write_apply, toNat_sub_add_ofNat _ _ (by omega)]
  have : i / 8 < n := by omega
  simp only [hi, decide_true, Bool.true_and, this, ite_true, BitVec.getLsbD_extractLsb']
  have : i % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

/-- `b .. b+k` and `a .. a+n` are disjoint (as ranges modulo 2^64). -/
def Sep (a : Addr) (n : Nat) (b : Addr) (k : Nat) : Prop :=
  n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat

instance (a : Addr) (n : Nat) (b : Addr) (k : Nat) : Decidable (Sep a n b k) := by
  unfold Sep; infer_instance

theorem Sep.symm {a b : Addr} {n k : Nat} (h : Sep a n b k) : Sep b k a n := ⟨h.2, h.1⟩

theorem Sep.not_lt {a b : Addr} {n k : Nat} (h : Sep a n b k) (j : Nat) (hj : j < k) :
    ¬ (b + BitVec.ofNat 64 j - a).toNat < n := by
  obtain ⟨h1, h2⟩ := h
  rw [show b + BitVec.ofNat 64 j - a = (b - a) + BitVec.ofNat 64 j by abel]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  have ha := a.isLt; have hb := b.isLt
  omega

/-- Reading memory untouched by a write. -/
theorem read_write_sep (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (b : Addr) (k : Nat)
    (h : Sep a n b k) : (m.write a n v).read b k = m.read b k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read, getLsbD_read, write_apply]
  rw [if_neg (h.not_lt (i / 8) (by omega))]

/-- Reading a sub-range of a region that was just written. -/
theorem read_write_within (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (k w : Nat)
    (hk : k + w ≤ n) (hn : n ≤ 2 ^ 64) :
    (m.write a n v).read (a + BitVec.ofNat 64 k) w = v.extractLsb' (8 * k) (8 * w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read, write_apply, BitVec.getLsbD_extractLsb']
  have e : a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (k + i / 8) := by
    rw [show a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) by abel]
    apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have : k + i / 8 < n := by omega
  simp only [hi, decide_true, Bool.true_and, this, ite_true, BitVec.getLsbD_extractLsb']
  have : i % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

/-- A read of a sub-range of a larger read. -/
theorem read_sub (m : Mem) (a : Addr) (n k w : Nat) (hk : k + w ≤ n) (hn : n ≤ 2 ^ 64) :
    m.read (a + BitVec.ofNat 64 k) w = (m.read a n).extractLsb' (8 * k) (8 * w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read, BitVec.getLsbD_extractLsb', getLsbD_read]
  have : 8 * k + i < 8 * n := by omega
  simp only [hi, decide_true, Bool.true_and, this]
  have e1 : (8 * k + i) / 8 = k + i / 8 := by omega
  have e2 : (8 * k + i) % 8 = i % 8 := by omega
  rw [e1, e2, BitVec.add_assoc]
  congr 3
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

/-- Little-endian write of a `w`-bit value (`w` a multiple of 8). -/
def writeW (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) : Mem :=
  m.write a (w / 8) (v.setWidth (8 * (w / 8)))

theorem readW_writeW_same (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (hw : w % 8 = 0)
    (hn : w / 8 ≤ 2 ^ 64) : (m.writeW a v).readW a w = v := by
  rw [readW, writeW, read_write_same _ _ _ _ hn]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth]
  have : i < 8 * (w / 8) := by omega
  simp [this, hi]

theorem readW_writeW_sep (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (b : Addr) (w' : Nat)
    (h : Sep a (w / 8) b (w' / 8)) : (m.writeW a v).readW b w' = m.readW b w' := by
  rw [readW, writeW, read_write_sep _ _ _ _ _ _ h, readW]

theorem writeW_apply_sep (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (b : Addr)
    (h : Sep a (w / 8) b 1) : (m.writeW a v) b = m b := by
  have := h.not_lt 0 (by omega)
  simp only [writeW, write_apply]
  rw [if_neg (by simpa using this)]

end Mem

/-! ## Regions -/

/-- A contiguous range of memory `[base, base + len)`. -/
structure Region where
  base : Addr
  len : Nat
  deriving DecidableEq, Repr

/-- The access `[a, a+n)` lies within region `r`. -/
def Region.Contains (r : Region) (a : Addr) (n : Nat) : Prop :=
  (a - r.base).toNat + n ≤ r.len

instance (r : Region) (a : Addr) (n : Nat) : Decidable (r.Contains a n) := by
  unfold Region.Contains; infer_instance

/-- The access `[a, a+n)` lies within one of the regions. -/
def InRegions (rs : List Region) (a : Addr) (n : Nat) : Prop := ∃ r ∈ rs, r.Contains a n

instance (rs : List Region) (a : Addr) (n : Nat) : Decidable (InRegions rs a n) := by
  unfold InRegions; infer_instance

theorem Region.contains_offset (b : Addr) (len k n : Nat) (h : k + n ≤ len) (hl : len < 2 ^ 64) :
    (Region.mk b len).Contains (b + BitVec.ofNat 64 k) n := by
  unfold Region.Contains
  simp only
  rw [Mem.toNat_sub_add_ofNat _ _ (by omega)]; exact h

end CC
