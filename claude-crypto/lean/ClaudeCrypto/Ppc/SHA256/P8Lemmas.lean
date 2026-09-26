import ClaudeCrypto.Ppc.SHA256.P8
import ClaudeCrypto.Ppc.VecLemmas
import ClaudeCrypto.Spec.SHA256Lemmas

/-!
# The vector computations of the ppc64le SHA-256 code in terms of the specification

Abstract (register-free) lemmas: the value computed by one round in `word[0]`
is one FIPS 180-4 round, and `schedCode` computes the next four words of the
message schedule.
-/

namespace CC.Ppc.SHA256P8

open CC.Spec.SHA256

theorem sigma0_eq (x : Word) : shaSigmaWord false false x = sigma0 x := rfl
theorem sigma1_eq (x : Word) : shaSigmaWord false true x = sigma1 x := rfl
theorem SIGMA0_eq (x : Word) : shaSigmaWord true false x = SIGMA0 x := rfl
theorem SIGMA1_eq (x : Word) : shaSigmaWord true true x = SIGMA1 x := rfl

theorem testBit_15 (i : Nat) (h : i < 4) : Nat.testBit 15 i = true := by
  interval_cases i <;> rfl
theorem testBit_0 (i : Nat) : Nat.testBit 0 i = false := Nat.zero_testBit i

theorem ch_eq (e f g : Word) : (g &&& ~~~e) ||| (f &&& e) = Ch e f g := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

theorem maj_eq (a b c : Word) : (b &&& ~~~(a ^^^ b)) ||| (c &&& (a ^^^ b)) = Maj a b c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-! ## One round -/

/-- The new `e` computed by `roundCode` (from the old `d`). -/
def newE (d e f g h kw : BitVec 128) : BitVec 128 :=
  vadduwm (vadduwm d (vadduwm (vadduwm h kw) (vsel g f e))) (vshasigmaw e true 15)

/-- The new `a` computed by `roundCode` (from the old `h`). -/
def newA (a b c e f g h kw : BitVec 128) : BitVec 128 :=
  vadduwm (vadduwm (vadduwm (vadduwm (vadduwm h kw) (vsel g f e)) (vshasigmaw e true 15))
    (vsel b c (a ^^^ b))) (vshasigmaw a true 0)

/-- The working variables `v` in `word[0]` of eight vectors. -/
structure VarsW (a b c d e f g h : BitVec 128) (v : Vars) : Prop where
  a : word a 0 = v.a
  b : word b 0 = v.b
  c : word c 0 = v.c
  d : word d 0 = v.d
  e : word e 0 = v.e
  f : word f 0 = v.f
  g : word g 0 = v.g
  h : word h 0 = v.h

/-- One round, with `K + W` in `word[0]` of `kw`, is one FIPS 180-4 round. -/
theorem round_word (a b c d e f g h kw : BitVec 128) (v : Vars) (k w : Word)
    (hv : VarsW a b c d e f g h v) (hkw : word kw 0 = k + w) :
    VarsW (newA a b c e f g h kw) a b c (newE d e f g h kw) e f g (Spec.SHA256.round v k w) := by
  have e1 : word (vshasigmaw e true 15) 0 = SIGMA1 v.e := by
    rw [word_vshasigmaw_0, testBit_15 3 (by decide), hv.e]; rfl
  have e0 : word (vshasigmaw a true 0) 0 = SIGMA0 v.a := by
    rw [word_vshasigmaw_0, testBit_0, hv.a]; rfl
  have ech : word (vsel g f e) 0 = Ch v.e v.f v.g := by
    rw [word_vsel_0, hv.e, hv.f, hv.g, ch_eq]
  have emj : word (vsel b c (a ^^^ b)) 0 = Maj v.a v.b v.c := by
    rw [word_vsel_0, word_xor, hv.a, hv.b, hv.c, maj_eq]
  refine ⟨?_, hv.a, hv.b, hv.c, ?_, hv.e, hv.f, hv.g⟩
  · simp only [newA, word_vadduwm_0, e1, e0, ech, emj, hv.h, hkw, Spec.SHA256.round]; ac_rfl
  · simp only [newE, word_vadduwm_0, e1, ech, hv.h, hv.d, hkw, Spec.SHA256.round]; ac_rfl

/-! ## Message schedule -/

/-- The schedule words `W[4k .. 4k+3]` as a vector (`W[4k]` in `word[0]`). -/
def packW (W : Nat → Word) (k : Nat) : BitVec 128 :=
  w4 (W (4 * k)) (W (4 * k + 1)) (W (4 * k + 2)) (W (4 * k + 3))

/-- The value computed by `schedCode` into `wreg p`. -/
def schedVal (xa xb xc xd z : BitVec 128) : BitVec 128 :=
  let a1 := vadduwm xa (vshasigmaw (vsldoi xa xb 4) false 0)
  let a2 := vadduwm a1 (vsldoi xc xd 4)
  let a3 := vadduwm a2 (vshasigmaw (vsldoi xd z 8) false 15)
  vadduwm a3 (vshasigmaw (vsldoi z a3 8) false 15)

/-- The schedule recurrence for `W[4k+16 .. 4k+19]`. -/
def SchedRec (W : Nat → Word) (k : Nat) : Prop :=
  ∀ t, 4 * k + 16 ≤ t → t < 4 * k + 20 →
    W t = sigma1 (W (t - 2)) + W (t - 7) + sigma0 (W (t - 15)) + W (t - 16)

theorem sigma1_zero : sigma1 0 = 0 := by decide

theorem word_zero (i : Nat) : word 0 i = 0 := by simp [word]

theorem w4_zero : (0 : BitVec 128) = w4 0 0 0 0 := by decide

theorem sched_step (W : Nat → Word) (k : Nat) (hW : SchedRec W k) :
    schedVal (packW W k) (packW W (k + 1)) (packW W (k + 2)) (packW W (k + 3)) 0 = packW W (k + 4) := by
  simp only [schedVal, packW, w4_zero, vsldoi_4, vsldoi_8, word_w4_0, word_w4_1, word_w4_2, word_w4_3,
    vshasigmaw_eq, vadduwm_w4, testBit_0, testBit_15 _ (show 0 < 4 by decide),
    testBit_15 _ (show 1 < 4 by decide), testBit_15 _ (show 2 < 4 by decide),
    testBit_15 _ (show 3 < 4 by decide), sigma0_eq, sigma1_eq, sigma1_zero, add_zero]
  have i1 : 4 * (k + 1) = 4 * k + 4 := by ring
  have i2 : 4 * (k + 2) = 4 * k + 8 := by ring
  have i3 : 4 * (k + 3) = 4 * k + 12 := by ring
  have i4 : 4 * (k + 4) = 4 * k + 16 := by ring
  simp only [i1, i2, i3, i4, Nat.add_assoc, Nat.reduceAdd]
  have w16 := hW (4 * k + 16) (by omega) (by omega)
  have w17 := hW (4 * k + (16 + 1)) (by omega) (by omega)
  have w18 := hW (4 * k + (16 + 2)) (by omega) (by omega)
  have w19 := hW (4 * k + (16 + 3)) (by omega) (by omega)
  simp only [Nat.reduceAdd, show 4 * k + 16 - 2 = 4 * k + 14 by omega,
    show 4 * k + 16 - 7 = 4 * k + 9 by omega, show 4 * k + 16 - 15 = 4 * k + 1 by omega,
    show 4 * k + 16 - 16 = 4 * k by omega,
    show 4 * k + 17 - 2 = 4 * k + 15 by omega, show 4 * k + 17 - 7 = 4 * k + 10 by omega,
    show 4 * k + 17 - 15 = 4 * k + 2 by omega, show 4 * k + 17 - 16 = 4 * k + 1 by omega,
    show 4 * k + 18 - 2 = 4 * k + 16 by omega, show 4 * k + 18 - 7 = 4 * k + 11 by omega,
    show 4 * k + 18 - 15 = 4 * k + 3 by omega, show 4 * k + 18 - 16 = 4 * k + 2 by omega,
    show 4 * k + 19 - 2 = 4 * k + 17 by omega, show 4 * k + 19 - 7 = 4 * k + 12 by omega,
    show 4 * k + 19 - 15 = 4 * k + 4 by omega, show 4 * k + 19 - 16 = 4 * k + 3 by omega]
    at w16 w17 w18 w19
  have h16 : W (4 * k) + sigma0 (W (4 * k + 1)) + W (4 * k + 9) + sigma1 (W (4 * k + 14)) =
      W (4 * k + 16) := by rw [w16]; ac_rfl
  have h17 : W (4 * k + 1) + sigma0 (W (4 * k + 2)) + W (4 * k + 10) + sigma1 (W (4 * k + 15)) =
      W (4 * k + 17) := by rw [w17]; ac_rfl
  rw [h16, h17]
  congr 1
  · rw [w18]; ac_rfl
  · rw [w19]; ac_rfl

/-! ## Packing and unpacking the hash value -/

theorem word_vor_self (x : BitVec 128) (i : Nat) : word (x ||| x) i = word x i := by
  rw [BitVec.or_self]

theorem word_vsldoi_self (x : BitVec 128) :
    word (vsldoi x x 4) 0 = word x 1 ∧ word (vsldoi x x 8) 0 = word x 2 ∧
      word (vsldoi x x 12) 0 = word x 3 := by
  simp only [vsldoi_4, vsldoi_8, vsldoi_12, word_w4_0, and_self]

theorem pack_eq (a b c d : BitVec 128) :
    xxpermdi (vmrghw a b) (vmrghw c d) 0 = w4 (word a 0) (word b 0) (word c 0) (word d 0) := by
  rw [vmrghw_eq, vmrghw_eq, xxpermdi_0]

end CC.Ppc.SHA256P8
