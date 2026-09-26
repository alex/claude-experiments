import ClaudeCrypto.P384.Frame

/-!
# The constants table

`constVals_of_table`: if the constants table `constTable` is in memory at `r13`, the values
read by the program are the intended constants (`ConstVals`).
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- The little-endian value of the `n` bytes at `a`. -/
def lbytes (m : Mem) (a : Addr) : Nat → Nat
  | 0 => 0
  | n + 1 => lbytes m a n + (m (a + BitVec.ofNat 64 n)).toNat * 256 ^ n

theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem lbytes_succ' (m : Mem) (a : Addr) (n : Nat) :
    lbytes m a (n + 1) = (m a).toNat + 256 * lbytes m (a + 1) n := by
  induction n with
  | zero => simp [lbytes]
  | succ n ih =>
    rw [lbytes, ih, lbytes, show a + 1 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod, Nat.add_comm]]
    ring

theorem read_toNat (m : Mem) (a : Addr) (n : Nat) : (m.read a n).toNat = lbytes m a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Mem.read, toNat_append', ih, lbytes_succ']
    ring

theorem readW_toNat (m : Mem) (a : Addr) : (m.readW a 64).toNat = lbytes m a 8 := by
  rw [Mem.readW, BitVec.toNat_setWidth, read_toNat, Nat.mod_eq_of_lt]
  rw [← read_toNat]; exact (m.read a 8).isLt

theorem lbytes_add (m : Mem) (a : Addr) (p q : Nat) :
    lbytes m a (p + q) = lbytes m a p + 256 ^ p * lbytes m (a + BitVec.ofNat 64 p) q := by
  induction q with
  | zero => simp [lbytes]
  | succ q ih =>
    rw [← Nat.add_assoc, lbytes, ih, lbytes, addr_add_ofNat', pow_add]
    ring

theorem mval_lbytes (m : Mem) (a : Addr) (k : Nat) : lsum (mlimb m a) k = lbytes m a (8 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lsum_succ, ih, show 8 * (k + 1) = 8 * k + 8 by ring, lbytes_add, mlimb, readW_toNat,
      show 2 ^ (64 * k) = 256 ^ (8 * k) by rw [pow_mul, pow_mul]; norm_num]
    ring

/-- Bytes of a little-endian number. -/
theorem lbytes_of (m : Mem) (a : Addr) (x L : Nat)
    (h : ∀ j < L, m (a + BitVec.ofNat 64 j) = BitVec.ofNat 8 (x / 256 ^ j)) :
    lbytes m a L = x % 256 ^ L := by
  induction L with
  | zero => simp [lbytes, Nat.mod_one]
  | succ L ih =>
    have e : x % 256 ^ (L + 1) = x % 256 ^ L + 256 ^ L * (x / 256 ^ L % 256) := by
      rw [pow_succ]; exact Nat.mod_mul
    rw [lbytes, ih (fun j hj => h j (by omega)), h L (by omega), e]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    ring

/-- The bytes of the table at offset `c` are the `L`-byte little-endian encoding of `x`. -/
def TableAt (c L x : Nat) : Prop := ∀ j < L, constTable[c + j]! = BitVec.ofNat 8 (x / 256 ^ j)

section
variable (s : State) (h : ∀ j < constSize, s.mem (s.r 13 + BitVec.ofNat 64 j) = constTable[j]!)
include h

theorem table_bytes (c L x : Nat) (hc : c + L ≤ constSize) (ht : TableAt c L x) :
    ∀ j < L, s.mem (s.r 13 + BitVec.ofNat 64 c + BitVec.ofNat 64 j) = BitVec.ofNat 8 (x / 256 ^ j) := by
  intro j hj
  rw [addr_add_ofNat', h _ (by omega), ht j hj]

theorem cval_of (c x : Nat) (hc : c + 48 ≤ constSize) (ht : TableAt c 48 x) (hx : x < 2 ^ 384) :
    cval s c = x := by
  unfold cval mval
  rw [mval_lbytes, lbytes_of _ _ x _ (table_bytes s h c 48 x hc ht), Nat.mod_eq_of_lt
    (by rw [show (256 : Nat) ^ (8 * 6) = 2 ^ 384 by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul]]; exact hx)]

theorem cword_of (c x : Nat) (hc : c + 8 ≤ constSize) (ht : TableAt c 8 x) (hx : x < 2 ^ 64) :
    cword s c = x := by
  unfold cword
  rw [readW_toNat, lbytes_of _ _ x _ (table_bytes s h c 8 x hc ht), Nat.mod_eq_of_lt
    (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul]]; exact hx)]

end

theorem tab_P : TableAt cP 48 p := by unfold TableAt; decide +kernel
theorem tab_MpP : TableAt cMpP 8 (negInv64 p) := by unfold TableAt; decide +kernel
theorem tab_N : TableAt cN 48 n := by unfold TableAt; decide +kernel
theorem tab_MpN : TableAt cMpN 8 (negInv64 n) := by unfold TableAt; decide +kernel
theorem tab_R2P : TableAt cR2P 48 (R * R % p) := by unfold TableAt; decide +kernel
theorem tab_OneP : TableAt cOneP 48 (R % p) := by unfold TableAt; decide +kernel
theorem tab_Gx : TableAt cGx 48 (Gx * R % p) := by unfold TableAt; decide +kernel
theorem tab_Gy : TableAt cGy 48 (Gy * R % p) := by unfold TableAt; decide +kernel
theorem tab_B : TableAt cB 48 (b * R % p) := by unfold TableAt; decide +kernel
theorem tab_R2N : TableAt cR2N 48 (R * R % n) := by unfold TableAt; decide +kernel
theorem tab_OneN : TableAt cOneN 48 (R % n) := by unfold TableAt; decide +kernel
theorem tab_Nm2 : TableAt cNm2 48 (n - 2) := by unfold TableAt; decide +kernel
theorem tab_Nm : TableAt cNm 48 (n * R % p) := by unfold TableAt; decide +kernel
theorem tab_Pmn : TableAt cPmn 48 (p - n) := by unfold TableAt; decide +kernel

/-- **The constants table.**  If the bytes of `constTable` are at `r13`, the program's
constants have their intended values. -/
theorem constVals_of_table (s : State)
    (h : ∀ j < constSize, s.mem (s.r 13 + BitVec.ofNat 64 j) = constTable[j]!) : ConstVals s where
  hp := cval_of s h _ _ (by decide) tab_P (by decide +kernel)
  hmpP := cword_of s h _ _ (by decide) tab_MpP (by decide +kernel)
  hn := cval_of s h _ _ (by decide) tab_N (by decide +kernel)
  hmpN := cword_of s h _ _ (by decide) tab_MpN (by decide +kernel)
  hr2p := cval_of s h _ _ (by decide) tab_R2P (by decide +kernel)
  honeP := cval_of s h _ _ (by decide) tab_OneP (by decide +kernel)
  hgx := cval_of s h _ _ (by decide) tab_Gx (by decide +kernel)
  hgy := cval_of s h _ _ (by decide) tab_Gy (by decide +kernel)
  hb := cval_of s h _ _ (by decide) tab_B (by decide +kernel)
  hr2n := cval_of s h _ _ (by decide) tab_R2N (by decide +kernel)
  honeN := cval_of s h _ _ (by decide) tab_OneN (by decide +kernel)
  hnm2 := cval_of s h _ _ (by decide) tab_Nm2 (by decide +kernel)
  hnm := cval_of s h _ _ (by decide) tab_Nm (by decide +kernel)
  hpmn := cval_of s h _ _ (by decide) tab_Pmn (by decide +kernel)

end CC.P384
