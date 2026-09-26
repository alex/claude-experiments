import ClaudeCrypto.P384.MainSpec

/-! # Helpers for the machine-level P-384 theorems (`X86/P384Main.lean`, `Arm/P384Main.lean`) -/

namespace CC.P384

open CC.Limb CC.Spec.P384

theorem inBytes_congr {m m' : Mem} {F : Addr} {L : Nat} (hag : Mem.Agree m m' ⟨F, L⟩) (a : Addr) (len : Nat)
    (hs : Mem.Sep F L a len) (hL : 0 < L) : inBytes m' a len = inBytes m a len := by
  unfold inBytes
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  exact hag.apply _ (by simpa using hs.mono 0 j L 1 (by omega) (by omega) hL (by omega))

/-- `verifyMem` only depends on the input bytes. -/
theorem verifyMem_congr {m m' : Mem} {F : Addr} {L : Nat} (hag : Mem.Agree m m' ⟨F, L⟩) (hL : 0 < L)
    (pk dg sg : Addr) (h1 : Mem.Sep F L pk 96) (h2 : Mem.Sep F L dg 48) (h3 : Mem.Sep F L sg 96) :
    verifyMem m' pk dg sg = verifyMem m pk dg sg := by
  unfold verifyMem
  rw [inBytes_congr hag pk 48 (by simpa using h1.mono 0 0 L 48 (by omega) (by omega) hL (by omega)) hL,
    inBytes_congr hag (pk + 48#64) 48 (by simpa using h1.mono 0 48 L 48 (by omega) (by omega) hL (by omega)) hL,
    inBytes_congr hag dg 48 h2 hL,
    inBytes_congr hag sg 48 (by simpa using h3.mono 0 0 L 48 (by omega) (by omega) hL (by omega)) hL,
    inBytes_congr hag (sg + 48#64) 48 (by simpa using h3.mono 0 48 L 48 (by omega) (by omega) hL (by omega)) hL]

theorem within_head (F : Addr) (L l : Nat) (rest : List Region) (hl : l ≤ L) (hL : L < 2 ^ 64) :
    Within (⟨F, L⟩ :: rest) F l :=
  ⟨⟨F, L⟩, List.mem_cons_self .., hL, (region_contains_self _ _ _).mpr hl⟩

theorem Within.shrink {rs : List Region} {a : Addr} {L l : Nat} (h : Within rs a L) (hl : l ≤ L) :
    Within rs a l := by
  obtain ⟨r, hr, h1, h2⟩ := h
  exact ⟨r, hr, h1, by unfold Region.Contains at *; omega⟩

theorem sep_shrink {F b : Addr} {L L' n : Nat} (h : Mem.Sep F L b n) (hl : L' ≤ L) (hL' : 0 < L') (hn : 0 < n) :
    Mem.Sep F L' b n := by
  simpa using h.mono 0 0 L' n (by omega) (by omega) hL' hn

end CC.P384
