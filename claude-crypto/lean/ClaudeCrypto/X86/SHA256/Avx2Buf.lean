import ClaudeCrypto.X86.SHA256.Avx2Sched
import ClaudeCrypto.Common.MemLemmas

/-! # AVX2 SHA-256: the `W + K` stack buffer and the constant tables -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

theorem readW_writeW_lane (m : Mem) (a : Addr) (v : BitVec 256) (i : Nat) (hi : i < 8) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * i)) 32 = lane 32 v i := by
  unfold Mem.readW Mem.writeW
  rw [Mem.read_write_within _ _ _ _ (4 * i) 4 (by omega) (by decide)]
  show setWidth 32 (extractLsb' (8 * (4 * i)) 32 (setWidth 256 v)) = extractLsb' (32 * i) 32 v
  apply eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_setWidth, getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    show 8 * (4 * i) + k < 256 by omega]
  congr 1; omega

theorem readW_eq_lanes (m : Mem) (a : Addr) (f : Nat → BitVec 8)
    (h : ∀ j < 32, m (a + BitVec.ofNat 64 j) = f j) : m.readW a 256 = lanes 32 f := by
  unfold Mem.readW
  show setWidth 256 (m.read a 32) = _
  apply eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_setWidth, Mem.getLsbD_read, getLsbD_lanes, hk, decide_true, Bool.true_and,
    show k < 8 * 32 by omega]
  rw [h _ (by omega)]

/-- Schedule word function of lane `L`. -/
def WL (WA WB : Nat → Word) (L t : Nat) : Word := if L = 0 then WA t else WB t

/-- The stack buffer holds `W[t] + K[t]` for the first `G` groups of both lanes. -/
def BufInv (WA WB : Nat → Word) (m : Mem) (sp : Addr) (G : Nat) : Prop :=
  ∀ t < 4 * G, ∀ L < 2, m.readW (sp + BitVec.ofNat 64 (wkOff L t)) 32 = WL WA WB L t + K[t]!

theorem addr_add_ofNat (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem BufInv.step {WA WB : Nat → Word} {m : Mem} {sp : Addr} {G : Nat} (hb : BufInv WA WB m sp G)
    (hG : G < 16) (x kv : BitVec 256) (hx : HoldsGroup x WA WB G)
    (hk : ∀ i < 8, lane 32 kv i = K[4 * G + i % 4]!) :
    BufInv WA WB (m.writeW (sp + BitVec.ofNat 64 (32 * G)) (vpadddV x kv)) sp (G + 1) := by
  intro t ht L hL
  by_cases h : t < 4 * G
  · rw [Mem.readW_writeW_sep', hb t h L hL]
    · rw [addr_add_sub_add]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, wkOff]
      rw [Nat.mod_eq_of_lt (a := 32 * G) (by omega),
        Nat.mod_eq_of_lt (a := 32 * (t / 4) + 4 * (t % 4) + 16 * L) (by omega)]
      omega
    · rw [addr_add_sub_add]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, wkOff]
      rw [Nat.mod_eq_of_lt (a := 32 * G) (by omega),
        Nat.mod_eq_of_lt (a := 32 * (t / 4) + 4 * (t % 4) + 16 * L) (by omega)]
      omega
  · have e : wkOff L t = 32 * G + 4 * (t % 4 + 4 * L) := by unfold wkOff; omega
    rw [e, ← addr_add_ofNat, readW_writeW_lane _ _ _ _ (by omega), lane_vpaddd _ _ _ (by omega),
      hx _ (by omega), hk _ (by omega)]
    have e2 : (t % 4 + 4 * L) % 4 = t % 4 := by omega
    have e3 : 4 * G + t % 4 = t := by omega
    rw [e2, e3]
    simp only [sel, WL]
    interval_cases L <;> simp [show t % 4 < 4 by omega]

end CC.X86.SHA256Avx2
