import ClaudeCrypto.P384.Prog
import ClaudeCrypto.Spec.P384Montgomery

/-!
# The frame and the constants table

`Inv s` collects the facts about the frame (at `r14`) and the constants table
(at `r13`) that hold throughout the verification routine; `Frm s q` says that
`q` differs from `s` only inside the frame; `Eff W s q` additionally says which
slots may have changed.  Every piece of the program is specified by these.
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

def constSize : Nat := 592

/-- Frame slot `i` as a number. -/
def sv (s : State) (i : Nat) : Nat := slotVal 0 s i

/-- The loop counter. -/
def cnt (s : State) : BitVec 64 := s.mem.readW (s.r 14 + BitVec.ofNat 64 cntOff) 64

/-- The 6-limb constant at byte `c` of the table. -/
def cval (s : State) (c : Nat) : Nat := mval s.mem (s.r 13 + BitVec.ofNat 64 c) 6

/-- The 1-limb constant at byte `c` of the table. -/
def cword (s : State) (c : Nat) : Nat := (s.mem.readW (s.r 13 + BitVec.ofNat 64 c) 64).toNat

/-- `[a, a + len)` lies within a (not wrapping) region of `rs`. -/
def Within (rs : List Region) (a : Addr) (len : Nat) : Prop := ∃ r ∈ rs, r.len < 2 ^ 64 ∧ r.Contains a len

theorem Within.sub {rs : List Region} {a : Addr} {len : Nat} (h : Within rs a len) (k l : Nat)
    (hkl : k + l ≤ len) : InRegions rs (a + BitVec.ofNat 64 k) l := by
  obtain ⟨r, hr, hlen, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at *
  rw [show a + BitVec.ofNat 64 k - r.base = (a - r.base) + BitVec.ofNat 64 k by abel,
    BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem Within.mono_left {rs : List Region} {a : Addr} {len : Nat} (h : Within rs a len) (rs' : List Region) :
    Within (rs' ++ rs) a len := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, List.mem_append_right _ hr, h1, h2⟩

theorem Within.mono_right {rs : List Region} {a : Addr} {len : Nat} (h : Within rs a len) (rs' : List Region) :
    Within (rs ++ rs') a len := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, List.mem_append_left _ hr, h1, h2⟩

/-- The values of the constants. -/
structure ConstVals (s : State) : Prop where
  hp : cval s cP = p
  hmpP : cword s cMpP = negInv64 p
  hn : cval s cN = n
  hmpN : cword s cMpN = negInv64 n
  hr2p : cval s cR2P = R * R % p
  honeP : cval s cOneP = R % p
  hgx : cval s cGx = Gx * R % p
  hgy : cval s cGy = Gy * R % p
  hb : cval s cB = b * R % p
  hr2n : cval s cR2N = R * R % n
  honeN : cval s cOneN = R % n
  hnm2 : cval s cNm2 = n - 2
  hnm : cval s cNm = n * R % p
  hpmn : cval s cPmn = p - n

structure Inv (s : State) : Prop where
  fr : Within s.wr (s.r 14) frameSize
  cs : Within s.rd (s.r 13) constSize
  sep : Mem.Sep (s.r 14) frameSize (s.r 13) constSize
  vals : ConstVals s

/-- `q` differs from `s` only inside the frame. -/
structure Frm (s q : State) : Prop where
  r13 : q.r 13 = s.r 13
  r14 : q.r 14 = s.r 14
  rd : q.rd = s.rd
  wr : q.wr = s.wr
  labels : q.labels = s.labels
  agree : Mem.Agree s.mem q.mem ⟨s.r 14, frameSize⟩

theorem Frm.refl (s : State) : Frm s s := ⟨rfl, rfl, rfl, rfl, rfl, Mem.Agree.refl _ _⟩

theorem Frm.trans {s q u : State} (h1 : Frm s q) (h2 : Frm q u) : Frm s u :=
  ⟨h2.r13.trans h1.r13, h2.r14.trans h1.r14, h2.rd.trans h1.rd, h2.wr.trans h1.wr,
    h2.labels.trans h1.labels, h1.agree.trans (by have := h2.agree; rwa [h1.r14] at this)⟩

theorem _root_.CC.Mem.Agree.widen {m m' : Mem} {b : Addr} {l l' : Nat} (h : Mem.Agree m m' ⟨b, l⟩) (hl : l ≤ l') :
    Mem.Agree m m' ⟨b, l'⟩ := fun a ha => h a (fun hc => ha (by unfold Region.Contains at *; simp only at *; omega))

theorem cval_congr {s q : State} (h13 : q.r 13 = s.r 13) (hag : Mem.Agree s.mem q.mem ⟨s.r 14, frameSize⟩)
    (hsep : Mem.Sep (s.r 14) frameSize (s.r 13) constSize) (c : Nat) (hc : c + 48 ≤ constSize) :
    cval q c = cval s c := by
  unfold cval mval; rw [h13]; apply lsum_congr; intro k hk
  unfold mlimb; rw [addr_add_ofNat']
  exact congrArg BitVec.toNat (hag.readW _ _ (by
    have := hsep.mono 0 (c + 8 * k) frameSize 8 (by omega) (by omega) (by decide) (by decide)
    simpa using this))

theorem cword_congr {s q : State} (h13 : q.r 13 = s.r 13) (hag : Mem.Agree s.mem q.mem ⟨s.r 14, frameSize⟩)
    (hsep : Mem.Sep (s.r 14) frameSize (s.r 13) constSize) (c : Nat) (hc : c + 8 ≤ constSize) :
    cword q c = cword s c := by
  unfold cword; rw [h13]
  exact congrArg BitVec.toNat (hag.readW _ _ (by
    have := hsep.mono 0 c frameSize 8 (by omega) (by omega) (by decide) (by decide)
    simpa using this))

theorem Inv.frm {s q : State} (h : Inv s) (hf : Frm s q) : Inv q := by
  have cv := fun c hc => cval_congr hf.r13 hf.agree h.sep c hc
  have cw := fun c hc => cword_congr hf.r13 hf.agree h.sep c hc
  have v := h.vals
  refine ⟨by rw [hf.wr, hf.r14]; exact h.fr, by rw [hf.rd, hf.r13]; exact h.cs,
    by rw [hf.r13, hf.r14]; exact h.sep, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [cv _ (by decide)]; exact v.hp
  · rw [cw _ (by decide)]; exact v.hmpP
  · rw [cv _ (by decide)]; exact v.hn
  · rw [cw _ (by decide)]; exact v.hmpN
  · rw [cv _ (by decide)]; exact v.hr2p
  · rw [cv _ (by decide)]; exact v.honeP
  · rw [cv _ (by decide)]; exact v.hgx
  · rw [cv _ (by decide)]; exact v.hgy
  · rw [cv _ (by decide)]; exact v.hb
  · rw [cv _ (by decide)]; exact v.hr2n
  · rw [cv _ (by decide)]; exact v.honeN
  · rw [cv _ (by decide)]; exact v.hnm2
  · rw [cv _ (by decide)]; exact v.hnm
  · rw [cv _ (by decide)]; exact v.hpmn

/-- The effect of a piece of code: only the frame changes, only the slots `W` change,
and the counter is kept. -/
structure Eff (W : List Nat) (s q : State) : Prop where
  frm : Frm s q
  keep : ∀ i < nSlots, i ∉ W → sv q i = sv s i
  cnt : cnt q = cnt s

theorem Eff.refl (s : State) : Eff [] s s := ⟨Frm.refl s, fun _ _ _ => rfl, rfl⟩

theorem Eff.trans {W₁ W₂ : List Nat} {s q u : State} (h1 : Eff W₁ s q) (h2 : Eff W₂ q u) : Eff (W₁ ++ W₂) s u :=
  ⟨h1.frm.trans h2.frm, fun i hi hw => by
    simp only [List.mem_append, not_or] at hw
    rw [h2.keep i hi hw.2, h1.keep i hi hw.1], h2.cnt.trans h1.cnt⟩

theorem Eff.mono {W W' : List Nat} {s q : State} (h : Eff W s q) (hW : ∀ i ∈ W, i ∈ W') : Eff W' s q :=
  ⟨h.frm, fun i hi hw => h.keep i hi (fun h' => hw (hW i h')), h.cnt⟩

/-! ## Addresses -/

theorem frame_sub (s : State) (h : Inv s) (k l : Nat) (hkl : k + l ≤ frameSize) :
    InRegions s.wr (s.r 14 + BitVec.ofNat 64 k) l := h.fr.sub k l hkl

theorem slot_in (s : State) (h : Inv s) (i : Nat) (hi : i < nSlots) (k : Nat) (hk : k < 6) :
    InRegions s.wr (s.r 14 + BitVec.ofNat 64 (FOp.off 0 i + 8 * k)) 8 :=
  frame_sub s h _ _ (by have : nSlots = 37 := rfl; have : frameSize = 1784 := rfl; simp only [FOp.off]; omega)

theorem const_in (s : State) (h : Inv s) (c : Nat) (hc : c + 8 ≤ constSize) :
    InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 c) 8 :=
  (h.cs.mono_right s.wr).sub c 8 hc

theorem slot_const_sep (s : State) (h : Inv s) (i : Nat) (hi : i < nSlots) (c : Nat) (hc : c + 8 ≤ constSize) :
    Mem.Sep (slotAddr 0 s i) 48 (s.r 13 + BitVec.ofNat 64 c) 8 := by
  unfold slotAddr
  exact h.sep.mono _ _ _ _ (by have : nSlots = 37 := rfl; have : frameSize = 1784 := rfl; simp only [FOp.off]; omega) hc (by decide) (by decide)

theorem negInv64_p : (negInv64 p * p + 1) % 2 ^ 64 = 0 := by decide +kernel
theorem negInv64_n : (negInv64 n * n + 1) % 2 ^ 64 = 0 := by decide +kernel

theorem Inv.layout {s : State} (h : Inv s) (offN offMp N : Nat) (hN : cval s offN = N)
    (hM : (cword s offMp * N + 1) % 2 ^ 64 = 0) (hoN : offN + 48 ≤ constSize) (hoM : offMp + 8 ≤ constSize)
    (hc : Nat.Coprime (2 ^ 384) N) : Layout offN offMp 0 nSlots N s :=
  ⟨hN, by decide, by unfold constSize at hoN; omega, fun i hi k hk => slot_in s h i hi k hk,
    fun k hk => const_in s h _ (by omega), const_in s h _ hoM,
    fun i hi k hk => slot_const_sep s h i hi _ (by omega), fun i hi => slot_const_sep s h i hi _ hoM, hM, hc⟩

theorem Inv.layoutP {s : State} (h : Inv s) : Layout cP cMpP 0 nSlots p s :=
  h.layout cP cMpP p h.vals.hp (by rw [h.vals.hmpP]; exact negInv64_p) (by decide) (by decide)
    (coprime_two_pow_p 384)

theorem Inv.layoutN {s : State} (h : Inv s) : Layout cN cMpN 0 nSlots n s :=
  h.layout cN cMpN n h.vals.hn (by rw [h.vals.hmpN]; exact negInv64_n) (by decide) (by decide)
    (coprime_two_pow_n 384)

/-- The slot area agrees ⇒ the frame agrees and the counter is kept. -/
theorem cnt_of_agree {s q : State} (h14 : q.r 14 = s.r 14)
    (hag : Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 0, 48 * nSlots⟩) : cnt q = cnt s := by
  unfold cnt; rw [h14]
  have e0 : s.r 14 + BitVec.ofNat 64 0 = s.r 14 := by simp
  rw [e0] at hag
  apply hag.readW
  have := sep_offsets (s.r 14) 0 cntOff (48 * nSlots) 8 (by left; unfold cntOff; omega) (by decide) (by decide)
    (by decide) (by decide)
  simpa using this

theorem frm_of_agree {s q : State} (h13 : q.r 13 = s.r 13) (h14 : q.r 14 = s.r 14) (hrd : q.rd = s.rd)
    (hwr : q.wr = s.wr) (hl : q.labels = s.labels)
    (hag : Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 0, 48 * nSlots⟩) : Frm s q := by
  refine ⟨h13, h14, hrd, hwr, hl, ?_⟩
  have e0 : s.r 14 + BitVec.ofNat 64 0 = s.r 14 := by simp
  rw [e0] at hag
  exact hag.widen (by unfold frameSize; omega)

end CC.P384
