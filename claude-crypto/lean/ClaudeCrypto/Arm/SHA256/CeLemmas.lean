import ClaudeCrypto.Arm.SHA256.Ce
import ClaudeCrypto.Arm.VecLemmas
import ClaudeCrypto.Spec.SHA256Lemmas

/-!
# The SHA-256 crypto-extension instructions in terms of the specification

Abstract lemmas: `sha256h`/`sha256h2` perform four rounds of FIPS 180-4
(given `Kₜ + Wₜ`), and `sha256su0` followed by `sha256su1` computes the next
four words of the message schedule.
-/

namespace CC.Arm.SHA256Ce

open CC.Spec.SHA256

/-- Working variables `a, b, c, d` as a vector (element 0 = `a`). -/
def abcd (v : Vars) : BitVec 128 := vec4 v.a v.b v.c v.d
/-- Working variables `e, f, g, h` as a vector (element 0 = `e`). -/
def efgh (v : Vars) : BitVec 128 := vec4 v.e v.f v.g v.h

/-- The round performed by one iteration of `SHA256hash`, where `w = Kₜ + Wₜ`. -/
def hwRound (v : Vars) (w : Word) : Vars :=
  let t := v.h + SHAhashSIGMA1 v.e + SHAchoose v.e v.f v.g + w
  { a := t + SHAhashSIGMA0 v.a + SHAmajority v.a v.b v.c, b := v.a, c := v.b, d := v.c,
    e := t + v.d, f := v.e, g := v.f, h := v.g }

def hw4 (v : Vars) (W : BitVec 128) : Vars :=
  hwRound (hwRound (hwRound (hwRound v (elem W 0)) (elem W 1)) (elem W 2)) (elem W 3)

theorem sha256hashIter_vars (W : BitVec 128) (e : Nat) (v : Vars) :
    sha256hashIter W e (abcd v, efgh v) = (abcd (hwRound v (elem W e)), efgh (hwRound v (elem W e))) := by
  simp only [sha256hashIter, abcd, efgh, vec4_extract0, vec4_extract32, vec4_extract64, vec4_extract96,
    append_extract_lo96, rotl_lo, rotl_hi, hwRound]

theorem sha256h_vars (v : Vars) (W : BitVec 128) :
    sha256hash (abcd v) (efgh v) W true = abcd (hw4 v W) := by
  simp only [sha256hash, sha256hashIter_vars, hw4, ite_true]

theorem sha256h2_vars (v : Vars) (W : BitVec 128) :
    sha256hash (abcd v) (efgh v) W false = efgh (hw4 v W) := by
  simp only [sha256hash, sha256hashIter_vars, hw4, Bool.false_eq_true, ite_false]

theorem choose_eq (x y z : Word) : SHAchoose x y z = Ch x y z := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [SHAchoose, Ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

theorem majority_eq (x y z : Word) : SHAmajority x y z = Maj x y z := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [SHAmajority, Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

/-- One hardware round with `w = K + W` is one FIPS 180-4 round. -/
theorem hwRound_eq (v : Vars) (k w : Word) : hwRound v (k + w) = Spec.SHA256.round v k w := by
  simp only [hwRound, Spec.SHA256.round, choose_eq, majority_eq]
  have e1 : SHAhashSIGMA1 v.e = SIGMA1 v.e := rfl
  have e0 : SHAhashSIGMA0 v.a = SIGMA0 v.a := rfl
  rw [e0, e1, Vars.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩ <;> ac_rfl

/-- Four hardware rounds on `K + W` (as `sha256h`/`sha256h2` compute them). -/
theorem hw4_eq (v : Vars) (k0 k1 k2 k3 w0 w1 w2 w3 : Word) :
    hw4 v (vadd32 (vec4 k0 k1 k2 k3) (vec4 w0 w1 w2 w3)) =
      round (round (round (round v k0 w0) k1 w1) k2 w2) k3 w3 := by
  simp only [hw4, vadd32_vec4, elem_vec4_0, elem_vec4_1, elem_vec4_2, elem_vec4_3, hwRound_eq]

/-! ## Message schedule -/

/-- The schedule words `W[4k .. 4k+3]` as a vector. -/
def packW (W : Nat → Word) (k : Nat) : BitVec 128 :=
  vec4 (W (4 * k)) (W (4 * k + 1)) (W (4 * k + 2)) (W (4 * k + 3))

theorem sha256su0_vec4 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    sha256su0 (vec4 a0 a1 a2 a3) (vec4 b0 b1 b2 b3) =
      vec4 (sigma0 a1 + a0) (sigma0 a2 + a1) (sigma0 a3 + a2) (sigma0 b0 + a3) := by
  simp only [sha256su0, append_extract_hi96, vec4_extract0, elem_vec4_0, elem_vec4_1, elem_vec4_2,
    elem_vec4_3]
  rfl

theorem sha256su1_vec4 (x0 x1 x2 x3 b0 b1 b2 b3 c0 c1 c2 c3 : Word) :
    sha256su1 (vec4 x0 x1 x2 x3) (vec4 b0 b1 b2 b3) (vec4 c0 c1 c2 c3) =
      vec4 (sigma1 c2 + x0 + b1) (sigma1 c3 + x1 + b2)
        (sigma1 (sigma1 c2 + x0 + b1) + x2 + b3) (sigma1 (sigma1 c3 + x1 + b2) + x3 + c0) := by
  simp only [sha256su1, append_extract_hi96, vec4_extract0, elem_vec4_0, elem_vec4_1, elem_vec4_2,
    elem_vec4_3, vec4_extract_hi64_lo, vec4_extract_hi64_hi, append32_extract0, append32_extract32]
  rfl

/-- The schedule recurrence for `W[4k+16 .. 4k+19]`. -/
def SchedRec (W : Nat → Word) (k : Nat) : Prop :=
  ∀ t, 4 * k + 16 ≤ t → t < 4 * k + 20 →
    W t = sigma1 (W (t - 2)) + W (t - 7) + sigma0 (W (t - 15)) + W (t - 16)

/-- `sha256su0` followed by `sha256su1` computes the next four schedule words. -/
theorem sched_step (W : Nat → Word) (k : Nat) (hW : SchedRec W k) :
    sha256su1 (sha256su0 (packW W k) (packW W (k + 1))) (packW W (k + 2)) (packW W (k + 3)) =
      packW W (k + 4) := by
  simp only [packW, sha256su0_vec4, sha256su1_vec4]
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
  have h16 : sigma1 (W (4 * k + 14)) + (sigma0 (W (4 * k + 1)) + W (4 * k)) + W (4 * k + 9) =
      W (4 * k + 16) := by rw [w16]; ac_rfl
  have h17 : sigma1 (W (4 * k + 15)) + (sigma0 (W (4 * k + 2)) + W (4 * k + 1)) + W (4 * k + 10) =
      W (4 * k + 17) := by rw [w17]; ac_rfl
  rw [h16, h17, w18, w19]
  exact congrArg₂ (vec4 _ _) (by ac_rfl) (by ac_rfl)

end CC.Arm.SHA256Ce
