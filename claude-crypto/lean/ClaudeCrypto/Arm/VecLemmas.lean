import ClaudeCrypto.Arm.Basic
import ClaudeCrypto.Common.MemLemmas

/-! # Lemmas about 128-bit vectors as four 32-bit elements (not part of the TCB) -/

namespace CC.Arm

set_option linter.unusedSimpArgs false

/-- Prove an equation between 128-bit (or smaller) vectors built from `vec4`,
`++`, `extractLsb'` and `rotateLeft`, bit by bit. -/
macro "lane_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, elem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft,
    BitVec.getLsbD_setWidth, Nat.reduceMod]
  split_ifs <;> (try simp (disch := omega) only [decide_eq_true, Bool.true_and, Bool.and_true,
    BitVec.getLsbD_of_ge, Bool.false_and, Bool.and_false]) <;>
    first | rfl | (congr 1; omega) | omega))

theorem vec4_extract0 (a b c d : BitVec 32) : (vec4 a b c d).extractLsb' 0 32 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp [show i < 32 by omega]

theorem vec4_extract32 (a b c d : BitVec 32) : (vec4 a b c d).extractLsb' 32 32 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp [show ¬ 32 + i < 32 by omega, show 32 + i - 32 = i by omega, hi]

theorem vec4_extract64 (a b c d : BitVec 32) : (vec4 a b c d).extractLsb' 64 32 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp [show ¬ 64 + i < 32 by omega, show ¬ 64 + i - 32 < 32 by omega, show 64 + i - 32 - 32 = i by omega, hi]

theorem vec4_extract96 (a b c d : BitVec 32) : (vec4 a b c d).extractLsb' 96 32 = d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp [show ¬ 96 + i < 32 by omega, show ¬ 96 + i - 32 < 32 by omega,
    show ¬ 96 + i - 32 - 32 < 32 by omega, show 96 + i - 32 - 32 - 32 = i by omega]

theorem elem_vec4_0 (a b c d : BitVec 32) : elem (vec4 a b c d) 0 = a := vec4_extract0 a b c d
theorem elem_vec4_1 (a b c d : BitVec 32) : elem (vec4 a b c d) 1 = b := vec4_extract32 a b c d
theorem elem_vec4_2 (a b c d : BitVec 32) : elem (vec4 a b c d) 2 = c := vec4_extract64 a b c d
theorem elem_vec4_3 (a b c d : BitVec 32) : elem (vec4 a b c d) 3 = d := vec4_extract96 a b c d

theorem vadd32_vec4 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    vadd32 (vec4 a0 a1 a2 a3) (vec4 b0 b1 b2 b3) = vec4 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  simp only [vadd32, elem_vec4_0, elem_vec4_1, elem_vec4_2, elem_vec4_3]

theorem vec4_ext (x : BitVec 128) : vec4 (elem x 0) (elem x 1) (elem x 2) (elem x 3) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vec4, elem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 32
  · simp [h1]
  by_cases h2 : i - 32 < 32
  · simp [h1, h2]; congr 1; omega
  by_cases h3 : i - 32 - 32 < 32
  · simp [h1, h2, h3]; congr 1; omega
  · simp [h1, h2, h3, show i - 32 - 32 - 32 < 32 by omega]; congr 1; omega

/-- Replacing the top element (`X<127:96> = x`). -/
theorem append_extract_lo96 (x a b c d : BitVec 32) :
    x ++ (vec4 a b c d).extractLsb' 0 96 = vec4 a b c x := by
  lane_tac

/-- `x : operand<127:32>`. -/
theorem append_extract_hi96 (x a b c d : BitVec 32) :
    x ++ (vec4 a b c d).extractLsb' 32 96 = vec4 b c d x := by
  lane_tac

theorem vec4_extract_hi64_lo (a b c d : BitVec 32) :
    ((vec4 a b c d).extractLsb' 64 64).extractLsb' 0 32 = c := by
  lane_tac

theorem vec4_extract_hi64_hi (a b c d : BitVec 32) :
    ((vec4 a b c d).extractLsb' 64 64).extractLsb' 32 32 = d := by
  lane_tac

theorem append32_extract0 (a b : BitVec 32) : (b ++ a).extractLsb' 0 32 = a := by
  lane_tac

theorem append32_extract32 (a b : BitVec 32) : (b ++ a).extractLsb' 32 32 = b := by
  lane_tac

set_option maxRecDepth 20000 in
/-- `ROL(Y : X, 32)` on four-element vectors. -/
theorem rotl_lo (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 32) :
    ((vec4 y0 y1 y2 y3 ++ vec4 x0 x1 x2 x3).rotateLeft 32).extractLsb' 0 128 = vec4 y3 x0 x1 x2 := by
  lane_tac

set_option maxRecDepth 20000 in
theorem rotl_hi (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 32) :
    ((vec4 y0 y1 y2 y3 ++ vec4 x0 x1 x2 x3).rotateLeft 32).extractLsb' 128 128 = vec4 x3 y0 y1 y2 := by
  lane_tac

/-! ## Memory -/

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

/-- A 128-bit little-endian load is four 32-bit little-endian loads. -/
theorem readW_128 (m : Mem) (a : Addr) :
    m.readW a 128 = vec4 (m.readW a 32) (m.readW (a + 4#64) 32) (m.readW (a + 8#64) 32) (m.readW (a + 12#64) 32) := by
  have h : ∀ k, k < 4 → m.readW (a + BitVec.ofNat 64 (4 * k)) 32 = elem (m.readW a 128) k := by
    intro k hk
    simp only [Mem.readW, elem]
    rw [Mem.read_sub m a 16 (4 * k) 4 (by omega) (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    simp only [show i < 8 * 4 by omega, decide_true, Bool.true_and, show 32 * k + i < 128 by omega]
    congr 1; omega
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
  rw [h0, h1, h2, h3, vec4_ext]

theorem rev8in32_readW (m : Mem) (a : Addr) :
    rev8in32 (m.readW a 32) = m a ++ m (a + 1) ++ m (a + 2) ++ m (a + 3) := by
  simp only [rev8in32, Mem.readW, Mem.read]
  have e2 : a + 1 + 1 = a + 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : a + 2 + 1 = a + 3 := by rw [BitVec.add_assoc]; rfl
  rw [e2, e3]
  generalize m a = b0; generalize m (a + 1) = b1; generalize m (a + 2) = b2; generalize m (a + 3) = b3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

theorem rev32_vec4 (a b c d : BitVec 32) :
    rev32 (vec4 a b c d) = vec4 (rev8in32 a) (rev8in32 b) (rev8in32 c) (rev8in32 d) := by
  simp only [rev32, elem_vec4_0, elem_vec4_1, elem_vec4_2, elem_vec4_3]

/-- Reading back one element of a 128-bit store. -/
theorem readW_writeW_vec4 (m : Mem) (a : Addr) (x0 x1 x2 x3 : BitVec 32) (k : Nat) (hk : k < 4) :
    (m.writeW a (vec4 x0 x1 x2 x3)).readW (a + BitVec.ofNat 64 (4 * k)) 32 =
      elem (vec4 x0 x1 x2 x3) k := by
  simp only [Mem.readW, Mem.writeW]
  rw [Mem.read_write_within _ _ _ _ _ _ (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [elem, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, show i < 8 * 4 by omega]
  simp only [show 8 * (4 * k) + i < 8 * (128 / 8) by omega, decide_true, Bool.true_and,
    show 32 * k + i < 128 by omega]
  congr 1; omega

end CC.Arm
