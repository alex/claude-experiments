import ClaudeCrypto.X86.SHA256.ShaNi
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.Spec.SHA256Lemmas

/-!
# The SHA-NI and SSE instructions in terms of the specification

Abstract lemmas over 128-bit values (not part of the TCB): `sha256rnds2`
performs two rounds of FIPS 180-4 (given `Kₜ + Wₜ`), `sha256msg1` + `palignr` +
`paddd` + `sha256msg2` compute the next four schedule words, and the shuffles
used for loading the message and rearranging the hash value do what they
should.
-/

namespace CC.X86.SHA256ShaNi

open BitVec CC.X86 CC.Spec.SHA256

set_option linter.unusedSimpArgs false

/-- Four 32-bit elements as a 128-bit vector (element 0 least significant). -/
def vec4 (e0 e1 e2 e3 : Word) : BitVec 128 := e3 ++ e2 ++ e1 ++ e0

/-- Prove an equation between 128-bit (or smaller) vectors built from `vec4`,
`++`, `extractLsb'`, `setWidth` and `>>>`, bit by bit. -/
macro "shani_lane_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, BitVec.lane, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, Nat.reduceMod]
  split_ifs <;> (try simp (disch := omega) only [decide_eq_true, Bool.true_and, Bool.and_true,
    BitVec.getLsbD_of_ge, Bool.false_and, Bool.and_false]) <;>
    first | rfl | (congr 1; omega) | omega))

theorem vec4_ex0 (a b c d : Word) : (vec4 a b c d).extractLsb' 0 32 = a := by shani_lane_tac
theorem vec4_ex32 (a b c d : Word) : (vec4 a b c d).extractLsb' 32 32 = b := by shani_lane_tac
theorem vec4_ex64 (a b c d : Word) : (vec4 a b c d).extractLsb' 64 32 = c := by shani_lane_tac
theorem vec4_ex96 (a b c d : Word) : (vec4 a b c d).extractLsb' 96 32 = d := by shani_lane_tac

theorem lane_vec4_0 (a b c d : Word) : lane 32 (vec4 a b c d) 0 = a := vec4_ex0 a b c d
theorem lane_vec4_1 (a b c d : Word) : lane 32 (vec4 a b c d) 1 = b := vec4_ex32 a b c d
theorem lane_vec4_2 (a b c d : Word) : lane 32 (vec4 a b c d) 2 = c := vec4_ex64 a b c d
theorem lane_vec4_3 (a b c d : Word) : lane 32 (vec4 a b c d) 3 = d := vec4_ex96 a b c d

theorem vec4_ext (x : BitVec 128) :
    vec4 (x.extractLsb' 0 32) (x.extractLsb' 32 32) (x.extractLsb' 64 32) (x.extractLsb' 96 32) = x := by
  shani_lane_tac

theorem lanes4 (f : Nat → Word) : (lanes (w := 32) 4 f : BitVec 128) = vec4 (f 0) (f 1) (f 2) (f 3) := by
  rw [← vec4_ext (lanes (w := 32) 4 f)]
  have h := fun i (hi : i < 4) => lane_lanes (w := 32) 4 f i hi
  simp only [lane] at h
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-! ## The SSE instructions -/

theorem padddX_vec4 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    padddX (vec4 a0 a1 a2 a3) (vec4 b0 b1 b2 b3) = vec4 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  rw [padddX, lanes4]
  simp only [lane_vec4_0, lane_vec4_1, lane_vec4_2, lane_vec4_3]

theorem pshufd_14 (a b c d : Word) : pshufd128 (vec4 a b c d) 14 = vec4 c d a a := by
  rw [pshufd128, lanes4]
  simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, lane_vec4_0, lane_vec4_2, lane_vec4_3]

theorem pshufd_27 (a b c d : Word) : pshufd128 (vec4 a b c d) 27 = vec4 d c b a := by
  rw [pshufd128, lanes4]
  simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, lane_vec4_0, lane_vec4_1, lane_vec4_2,
    lane_vec4_3]

set_option maxRecDepth 20000 in
theorem punpckl_vec4 (a b c d e f g h : Word) :
    punpcklqdqX (vec4 a b c d) (vec4 e f g h) = vec4 a b e f := by
  unfold punpcklqdqX; shani_lane_tac

set_option maxRecDepth 20000 in
theorem punpckh_vec4 (a b c d e f g h : Word) :
    punpckhqdqX (vec4 a b c d) (vec4 e f g h) = vec4 c d g h := by
  unfold punpckhqdqX; shani_lane_tac

set_option maxRecDepth 20000 in
theorem palignr4_vec4 (a b c d e f g h : Word) :
    palignr128 (vec4 a b c d) (vec4 e f g h) 4 = vec4 f g h a := by
  unfold palignr128; shani_lane_tac

/-! ## The SHA instructions -/

/-- Working variables `f, e, b, a` as a vector: the `ABEF` operand of `sha256rnds2`. -/
def abef (v : Vars) : BitVec 128 := vec4 v.f v.e v.b v.a
/-- Working variables `h, g, d, c` as a vector: the `CDGH` operand of `sha256rnds2`. -/
def cdgh (v : Vars) : BitVec 128 := vec4 v.h v.g v.d v.c

/-- One iteration of the loop of `SHA256RNDS2`, with `wk = Kₜ + Wₜ`. -/
def hwRound (v : Vars) (wk : Word) : Vars :=
  { a := shaCh v.e v.f v.g + shaSIGMA1 v.e + wk + v.h + shaMaj v.a v.b v.c + shaSIGMA0 v.a,
    b := v.a, c := v.b, d := v.c,
    e := shaCh v.e v.f v.g + shaSIGMA1 v.e + wk + v.h + v.d,
    f := v.e, g := v.f, h := v.g }

theorem rnds2_vars (v : Vars) (w0 w1 x y : Word) :
    sha256rnds2 (cdgh v) (abef v) (vec4 w0 w1 x y) = abef (hwRound (hwRound v w0) w1) := by
  simp only [sha256rnds2, cdgh, abef, vec4_ex0, vec4_ex32, vec4_ex64, vec4_ex96, hwRound]
  rfl

theorem hwRound_eq (v : Vars) (k w : Word) : hwRound v (k + w) = Spec.SHA256.round v k w := by
  simp only [hwRound, Spec.SHA256.round]
  have e0 : shaSIGMA0 v.a = SIGMA0 v.a := rfl
  have e1 : shaSIGMA1 v.e = SIGMA1 v.e := rfl
  have ec : shaCh v.e v.f v.g = Ch v.e v.f v.g := rfl
  have em : shaMaj v.a v.b v.c = Maj v.a v.b v.c := rfl
  rw [e0, e1, ec, em, Vars.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩ <;> ac_rfl

/-- Two rounds, as `sha256rnds2` computes them from `K + W`. -/
theorem rnds2_eq (v : Vars) (k0 k1 w0 w1 x y : Word) :
    sha256rnds2 (cdgh v) (abef v) (vec4 (k0 + w0) (k1 + w1) x y) =
      abef (round (round v k0 w0) k1 w1) := by
  rw [rnds2_vars, hwRound_eq, hwRound_eq]

/-- After two rounds, `CDGH` is the old `ABEF`. -/
theorem cdgh_round2 (v : Vars) (k0 k1 w0 w1 : Word) :
    cdgh (round (round v k0 w0) k1 w1) = abef v := rfl

theorem msg1_vec4 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    sha256msg1 (vec4 a0 a1 a2 a3) (vec4 b0 b1 b2 b3) =
      vec4 (a0 + sigma0 a1) (a1 + sigma0 a2) (a2 + sigma0 a3) (a3 + sigma0 b0) := by
  simp only [sha256msg1, vec4_ex0, vec4_ex32, vec4_ex64, vec4_ex96]
  rfl

theorem msg2_vec4 (x0 x1 x2 x3 c0 c1 c2 c3 : Word) :
    sha256msg2 (vec4 x0 x1 x2 x3) (vec4 c0 c1 c2 c3) =
      vec4 (x0 + sigma1 c2) (x1 + sigma1 c3) (x2 + sigma1 (x0 + sigma1 c2))
        (x3 + sigma1 (x1 + sigma1 c3)) := by
  simp only [sha256msg2, vec4_ex0, vec4_ex32, vec4_ex64, vec4_ex96]
  rfl

/-! ## Message schedule -/

/-- The schedule words `W[4k .. 4k+3]` as a vector. -/
def packW (W : Nat → Word) (k : Nat) : BitVec 128 :=
  vec4 (W (4 * k)) (W (4 * k + 1)) (W (4 * k + 2)) (W (4 * k + 3))

/-- The schedule recurrence for `W[4k+16 .. 4k+19]`. -/
def SchedRec (W : Nat → Word) (k : Nat) : Prop :=
  ∀ t, 4 * k + 16 ≤ t → t < 4 * k + 20 →
    W t = sigma1 (W (t - 2)) + W (t - 7) + sigma0 (W (t - 15)) + W (t - 16)

theorem schedRec_Wt (M : List Word) (j : Nat) : SchedRec (Wt M) j := by
  intro t h1 _; exact Wt_ge M t (by omega)

/-- `sha256msg1`, `palignr`, `paddd`, `sha256msg2` compute the next four schedule words. -/
theorem sched_step (W : Nat → Word) (k : Nat) (hW : SchedRec W k) :
    sha256msg2 (padddX (sha256msg1 (packW W k) (packW W (k + 1)))
        (palignr128 (packW W (k + 3)) (packW W (k + 2)) 4)) (packW W (k + 3)) =
      packW W (k + 4) := by
  simp only [packW, msg1_vec4, palignr4_vec4, padddX_vec4, msg2_vec4]
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
  rw [h16, h17, w18, w19]
  exact congrArg₂ (vec4 _ _) (by ac_rfl) (by ac_rfl)

/-! ## Loading bytes -/

theorem lanes_congr {w : Nat} (n : Nat) (f g : Nat → BitVec w) (h : ∀ i < n, f i = g i) :
    lanes n f = lanes n g := by
  apply eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_lanes, getLsbD_lanes]
  by_cases hw : w = 0
  · subst hw; simp at hj
  by_cases hjn : j < w * n
  · rw [h (j / w) (by rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith [Nat.mul_comm w n])]
  · simp [hjn]

theorem readW_lanes16 (m : Mem) (a : Addr) :
    m.readW a 128 = (lanes (w := 8) 16 fun i => m (a + BitVec.ofNat 64 i) : BitVec 128) := by
  unfold Mem.readW
  show setWidth 128 (m.read a 16) = _
  apply eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_setWidth, Mem.getLsbD_read, getLsbD_lanes, hk, decide_true, Bool.true_and,
    show k < 8 * 16 by omega]

theorem lanes16_vec4 (G : Nat → BitVec 8) :
    (lanes (w := 8) 16 G : BitVec 128) =
      vec4 (G 3 ++ G 2 ++ G 1 ++ G 0) (G 7 ++ G 6 ++ G 5 ++ G 4) (G 11 ++ G 10 ++ G 9 ++ G 8)
        (G 15 ++ G 14 ++ G 13 ++ G 12) := by
  apply eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_lanes, vec4, getLsbD_append]
  have hi' : i < 128 := hi
  interval_cases i <;> simp

/-- The byte-swap mask as loaded from memory. -/
def bswapX : BitVec 128 := lanes (w := 8) 16 fun i => bswapMask[i]!

/-- `pshufb` with the byte-swap mask reverses the bytes of each dword. -/
theorem pshufb_bswap (B : Nat → BitVec 8) :
    pshufb128 (lanes (w := 8) 16 B) bswapX =
      vec4 (B 0 ++ B 1 ++ B 2 ++ B 3) (B 4 ++ B 5 ++ B 6 ++ B 7) (B 8 ++ B 9 ++ B 10 ++ B 11)
        (B 12 ++ B 13 ++ B 14 ++ B 15) := by
  have h : pshufb128 (lanes (w := 8) 16 B) bswapX =
      (lanes (w := 8) 16 fun i => B ((i / 4) * 4 + 3 - i % 4) : BitVec 128) := by
    unfold pshufb128
    apply lanes_congr
    intro i hi
    have e : lane 8 bswapX i = bswapMask[i]! := lane_lanes 16 _ i hi
    rw [e]
    interval_cases i <;>
      simp (config := { decide := true }) [bswapMask, lane_lanes]
  rw [h, lanes16_vec4]

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem add_ofNat_add (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

end CC.X86.SHA256ShaNi
