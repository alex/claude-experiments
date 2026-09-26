import ClaudeCrypto.Common.Mem

/-! # Proof-support lemmas about memory and regions (not part of the TCB) -/

namespace CC

theorem Mem.read_congr (m m' : Mem) (a : Addr) (n : Nat)
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (a + BitVec.ofNat 64 i)) :
    m.read a n = m'.read a n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [Mem.getLsbD_read, Mem.getLsbD_read, h _ (by omega)]

/-- `m'` agrees with `m` outside region `r`. -/
def Mem.Agree (m m' : Mem) (r : Region) : Prop := ∀ a, ¬ r.Contains a 1 → m' a = m a

theorem Mem.Agree.refl (m : Mem) (r : Region) : Mem.Agree m m r := fun _ _ => rfl

theorem Mem.Agree.trans {m m' m'' : Mem} {r : Region} (h1 : Mem.Agree m m' r)
    (h2 : Mem.Agree m' m'' r) : Mem.Agree m m'' r := fun a ha => (h2 a ha).trans (h1 a ha)

theorem Region.contains_one_of (r : Region) (a : Addr) (n : Nat) (hc : r.Contains a n) (i : Nat)
    (hi : i < n) : r.Contains (a + BitVec.ofNat 64 i) 1 := by
  unfold Region.Contains at *
  rw [show a + BitVec.ofNat 64 i - r.base = (a - r.base) + BitVec.ofNat 64 i by abel]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 := Nat.mod_le i (2 ^ 64)
  have h2 := Nat.mod_le ((a - r.base).toNat + i % 2 ^ 64) (2 ^ 64)
  omega

theorem Mem.Agree.writeW {m m' : Mem} {r : Region} (h : Mem.Agree m m' r) (a : Addr) {w : Nat}
    (v : BitVec w) (hc : r.Contains a (w / 8)) : Mem.Agree m (m'.writeW a v) r := by
  intro x hx
  unfold Mem.writeW; rw [Mem.write_apply, if_neg, h x hx]
  intro hlt
  apply hx
  have := r.contains_one_of a (w / 8) hc (x - a).toNat hlt
  have e : a + BitVec.ofNat 64 (x - a).toNat = x := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; abel
  rwa [e] at this

theorem Mem.Sep.not_contains {base b : Addr} {len k : Nat} (h : Mem.Sep base len b k) (i : Nat)
    (hi : i < k) : ¬ (Region.mk base len).Contains (b + BitVec.ofNat 64 i) 1 := by
  unfold Region.Contains; simp only
  have := h.not_lt i hi
  omega

theorem Mem.Agree.readW {m m' : Mem} {base : Addr} {len : Nat} (h : Mem.Agree m m' ⟨base, len⟩)
    (b : Addr) (w : Nat) (hs : Mem.Sep base len b (w / 8)) : m'.readW b w = m.readW b w := by
  unfold Mem.readW; congr 1
  apply Mem.read_congr; intro i hi
  exact h _ (hs.not_contains i hi)

theorem Mem.Agree.apply {m m' : Mem} {base : Addr} {len : Nat} (h : Mem.Agree m m' ⟨base, len⟩)
    (b : Addr) (hs : Mem.Sep base len b 1) : m' b = m b := by
  have := h b (by simpa using hs.not_contains 0 (by omega))
  exact this

/-- `m'` agrees with `m` outside all of the regions `rs`. -/
def Mem.AgreeL (m m' : Mem) (rs : List Region) : Prop :=
  ∀ a, (∀ r ∈ rs, ¬ r.Contains a 1) → m' a = m a

theorem Mem.AgreeL.refl (m : Mem) (rs : List Region) : Mem.AgreeL m m rs := fun _ _ => rfl

theorem Mem.AgreeL.trans {m m' m'' : Mem} {rs : List Region} (h1 : Mem.AgreeL m m' rs)
    (h2 : Mem.AgreeL m' m'' rs) : Mem.AgreeL m m'' rs := fun a ha => (h2 a ha).trans (h1 a ha)

theorem Mem.AgreeL.of_agree {m m' : Mem} {r : Region} (rs : List Region) (h : Mem.Agree m m' r)
    (hr : r ∈ rs) : Mem.AgreeL m m' rs := fun a ha => h a (ha r hr)

theorem Mem.AgreeL.writeW {m m' : Mem} {rs : List Region} (h : Mem.AgreeL m m' rs) (r : Region)
    (hr : r ∈ rs) (a : Addr) {w : Nat} (v : BitVec w) (hc : r.Contains a (w / 8)) :
    Mem.AgreeL m (m'.writeW a v) rs := by
  intro x hx
  have := (Mem.Agree.writeW (m := m') (Mem.Agree.refl m' r) a v hc) x (hx r hr)
  rw [this, h x hx]

/-- Reading outside all the regions. -/
theorem Mem.AgreeL.readW {m m' : Mem} {rs : List Region} (h : Mem.AgreeL m m' rs) (b : Addr)
    (w : Nat) (hs : ∀ r ∈ rs, Mem.Sep r.base r.len b (w / 8)) : m'.readW b w = m.readW b w := by
  unfold Mem.readW; congr 1
  apply Mem.read_congr; intro i hi
  exact h _ (fun r hr => (hs r hr).not_contains i hi)

theorem Mem.AgreeL.apply {m m' : Mem} {rs : List Region} (h : Mem.AgreeL m m' rs) (b : Addr)
    (hs : ∀ r ∈ rs, Mem.Sep r.base r.len b 1) : m' b = m b := by
  have := h b (fun r hr => by simpa using (hs r hr).not_contains 0 (by omega))
  exact this

theorem Mem.AgreeL.mono {m m' : Mem} {rs rs' : List Region} (h : Mem.AgreeL m m' rs)
    (hsub : ∀ a, (∀ r' ∈ rs', ¬ r'.Contains a 1) → (∀ r ∈ rs, ¬ r.Contains a 1)) :
    Mem.AgreeL m m' rs' := fun a ha => h a (hsub a ha)

/-! ## Separation of sub-ranges -/

theorem toNat_sub_add_toNat_sub (a b : Addr) :
    (b - a).toNat + (a - b).toNat = 2 ^ 64 ∨ ((b - a).toNat = 0 ∧ (a - b).toNat = 0) := by
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_sub]
  omega

theorem Mem.Sep.mono {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) (i j n' k' : Nat)
    (hi : i + n' ≤ n) (hj : j + k' ≤ k) (hn' : 0 < n') (hk' : 0 < k') :
    Mem.Sep (a + BitVec.ofNat 64 i) n' (b + BitVec.ofNat 64 j) k' := by
  obtain ⟨h1, h2⟩ := h
  have hxy := toNat_sub_add_toNat_sub a b
  have hx := (b - a).isLt; have hy := (a - b).isLt
  have hsum : (b - a).toNat + (a - b).toNat = 2 ^ 64 := by omega
  unfold Mem.Sep
  have e1 : b + BitVec.ofNat 64 j - (a + BitVec.ofNat 64 i) =
      BitVec.ofNat 64 ((b - a).toNat + j - i) := by
    apply BitVec.eq_of_toNat_eq
    rw [show b + BitVec.ofNat 64 j - (a + BitVec.ofNat 64 i) = (b - a) + BitVec.ofNat 64 j - BitVec.ofNat 64 i by abel]
    generalize b - a = d at *
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e2 : a + BitVec.ofNat 64 i - (b + BitVec.ofNat 64 j) =
      BitVec.ofNat 64 ((a - b).toNat + i - j) := by
    apply BitVec.eq_of_toNat_eq
    rw [show a + BitVec.ofNat 64 i - (b + BitVec.ofNat 64 j) = (a - b) + BitVec.ofNat 64 i - BitVec.ofNat 64 j by abel]
    generalize a - b = d at *
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, e2, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  constructor
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem sep_add_add (x a b : Addr) (n k : Nat) : Mem.Sep (x + a) n (x + b) k ↔ Mem.Sep a n b k := by
  unfold Mem.Sep
  rw [show x + b - (x + a) = b - a by abel, show x + a - (x + b) = a - b by abel]

theorem sep_self_add (x b : Addr) (n k : Nat) : Mem.Sep x n (x + b) k ↔ Mem.Sep 0 n b k := by
  rw [← sep_add_add x 0 b, add_zero]

theorem sep_add_self (x a : Addr) (n k : Nat) : Mem.Sep (x + a) n x k ↔ Mem.Sep a n 0 k := by
  rw [← sep_add_add x a 0, add_zero]

theorem region_contains_add (x a : Addr) (len n : Nat) :
    (Region.mk x len).Contains (x + a) n ↔ a.toNat + n ≤ len := by
  unfold Region.Contains; simp only; rw [show x + a - x = a by abel]

theorem region_contains_self (x : Addr) (len n : Nat) :
    (Region.mk x len).Contains x n ↔ n ≤ len := by
  unfold Region.Contains; simp

theorem inRegions_cons (r : Region) (rs : List Region) (a : Addr) (n : Nat) :
    InRegions (r :: rs) a n ↔ r.Contains a n ∨ InRegions rs a n := by
  unfold InRegions; simp

theorem inRegions_append (rs rs' : List Region) (a : Addr) (n : Nat) :
    InRegions (rs ++ rs') a n ↔ InRegions rs a n ∨ InRegions rs' a n := by
  unfold InRegions; simp [or_and_right, exists_or]

theorem inRegions_nil (a : Addr) (n : Nat) : InRegions [] a n ↔ False := by
  unfold InRegions; simp

@[simp] theorem Mem.readW_writeW_same_32 (m : Mem) (a : Addr) (v : BitVec 32) :
    (m.writeW a v).readW a 32 = v := Mem.readW_writeW_same _ _ _ (by decide) (by decide)
@[simp] theorem Mem.readW_writeW_same_64 (m : Mem) (a : Addr) (v : BitVec 64) :
    (m.writeW a v).readW a 64 = v := Mem.readW_writeW_same _ _ _ (by decide) (by decide)
@[simp] theorem Mem.readW_writeW_same_128 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW a 128 = v := Mem.readW_writeW_same _ _ _ (by decide) (by decide)
@[simp] theorem Mem.readW_writeW_same_256 (m : Mem) (a : Addr) (v : BitVec 256) :
    (m.writeW a v).readW a 256 = v := Mem.readW_writeW_same _ _ _ (by decide) (by decide)

theorem add_sub_lit (x a b : Addr) : x + a - b = x + (a - b) := by abel
theorem addr_add_sub_cancel (x a : Addr) : x + a - x = a := by abel
theorem addr_sub_add_cancel (x a : Addr) : x - (x + a) = -a := by abel
theorem addr_add_sub_add (x a b : Addr) : x + a - (x + b) = a - b := by abel
theorem addr_sub_self (x : Addr) : x - x = 0 := by abel

/-- `readW_writeW_sep` with the separation condition unfolded (better for `simp`). -/
theorem Mem.readW_writeW_sep' (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (b : Addr) (w' : Nat)
    (h1 : w / 8 ≤ (b - a).toNat) (h2 : w' / 8 ≤ (a - b).toNat) :
    (m.writeW a v).readW b w' = m.readW b w' := Mem.readW_writeW_sep _ _ _ _ _ ⟨h1, h2⟩

end CC
