import ClaudeCrypto.Ppc.SHA256.P8Loop

/-!
# Correctness of `cc_sha256_blocks_ppc64le`

The main theorem, `correct`, states that running the function body from any
state satisfying the function's preconditions

* terminates without faulting — in particular it only reads the message, the
  data table (round constants and byte-swap mask) and the hash value, and only
  writes the hash value (memory safety);
* leaves FIPS 180-4's `hashBlocks H msg` in the hash-value buffer;
* preserves every register the ELFv2 ABI requires a function to preserve
  (`r1`, `r2`, `r13`–`r31`, `v20`–`v31`, `f14`–`f31`, CR2–CR4, and the link
  register); and
* leaves all memory outside the writable regions unchanged.
-/

namespace CC.Ppc.SHA256P8

open CC.Spec.SHA256

set_option linter.unusedSimpArgs false

theorem hashBlocks_eq (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    hashBlocks H msg = stateAfter H msg n := blocks_foldl H msg n hl

/-! ## Reading back the stored hash value -/

theorem readW_writeW_word (m : Mem) (st : Addr) (x : Word) (j k : Nat) (hj : j < 8) (hk : k < 8) :
    (m.writeW (st + BitVec.ofNat 64 (4 * j)) x).readW (st + BitVec.ofNat 64 (4 * k)) 32 =
      if j = k then x else m.readW (st + BitVec.ofNat 64 (4 * k)) 32 := by
  split
  · subst_vars; exact Mem.readW_writeW_same_32 _ _ _
  · apply Mem.readW_writeW_sep
    rw [sep_add_add]
    unfold Mem.Sep
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem addr_lit (st : Addr) (c : Nat) (x : BitVec 64) (hx : x = BitVec.ofNat 64 c) :
    st + x = st + BitVec.ofNat 64 c := by rw [hx]

/-- Reading back word `k` of the 32-byte hash value written by the two `stxvw4x`. -/
theorem read_state (m : Mem) (st : Addr) (x0 x1 x2 x3 x4 x5 x6 x7 : Word) (k : Nat) (hk : k < 8) :
    ((((((((m.writeW st x0).writeW (st + 4) x1).writeW (st + 8) x2).writeW (st + 12) x3).writeW
      (st + 16#64) x4).writeW (st + 16#64 + 4) x5).writeW (st + 16#64 + 8) x6).writeW
      (st + 16#64 + 12) x7).readW (st + BitVec.ofNat 64 (4 * k)) 32 = [x0, x1, x2, x3, x4, x5, x6, x7][k]! := by
  have a1 : st + 4 = st + BitVec.ofNat 64 (4 * 1) := rfl
  have a2 : st + 8 = st + BitVec.ofNat 64 (4 * 2) := rfl
  have a3 : st + 12 = st + BitVec.ofNat 64 (4 * 3) := rfl
  have a4 : st + 16#64 = st + BitVec.ofNat 64 (4 * 4) := rfl
  have a5 : st + 16#64 + 4 = st + BitVec.ofNat 64 (4 * 5) := by rw [BitVec.add_assoc]; rfl
  have a6 : st + 16#64 + 8 = st + BitVec.ofNat 64 (4 * 6) := by rw [BitVec.add_assoc]; rfl
  have a7 : st + 16#64 + 12 = st + BitVec.ofNat 64 (4 * 7) := by rw [BitVec.add_assoc]; rfl
  rw [a7, a6, a5, a4, a3, a2, a1,
    show ∀ (m' : Mem) (x : Word), m'.writeW st x = m'.writeW (st + BitVec.ofNat 64 (4 * 0)) x from
      fun _ _ => by simp]
  interval_cases k <;>
    simp (disch := decide) only [readW_writeW_word, ite_true, ite_false, reduceIte, Nat.reduceEqDiff,
      List.getElem!_cons_zero, List.getElem!_cons_succ, OfNat.ofNat_ne_zero]

theorem storePost_getG (s : State) (r : GReg) : (storePost s).getG r = s.getG r := rfl
theorem storePost_getV (s : State) (r : VReg) : (storePost s).getV r = s.getV r := rfl
theorem storePost_vsr (s : State) : (storePost s).vsr = s.vsr := rfl
theorem storePost_cr1to7 (s : State) : (storePost s).cr1to7 = s.cr1to7 := rfl
theorem storePost_lr (s : State) : (storePost s).lr = s.lr := rfl

/-! ## The main theorem -/

set_option maxHeartbeats 1000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_sha256_blocks_ppc64le`.**

`s` is the machine state on entry: `r3` points to the hash value `H`
(eight 32-bit words, native byte order), `r4` to the message `msg`
(`64 * n` bytes), and `r5 = n`; the program's data table (the 64 round
constants followed by the four words of the byte-swap mask) is at
`s.labels kLabel`.  The code may read the message and the table and read and
write the hash value (`s.rd`, `s.wr` may contain further regions). -/
theorem correct (s : State) (H : List Word) (msg : List (BitVec 8)) (n : Nat) (st inp : Addr)
    (hlen : msg.length = 64 * n) (hn : 64 * n < 2 ^ 64)
    (hr3 : s.getG .r3 = st) (hr4 : s.getG .r4 = inp) (hr5 : s.getG .r5 = BitVec.ofNat 64 n)
    (hHmem : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (hmsg : ∀ i < 64 * n, s.mem (inp + BitVec.ofNat 64 i) = msg[i]!)
    (hK : ∀ i < 68, s.mem.readW (s.labels kLabel + BitVec.ofNat 64 (4 * i)) 32 = table[i]!)
    (hrdm : ⟨inp, 64 * n⟩ ∈ s.rd) (hrdK : ⟨s.labels kLabel, 272⟩ ∈ s.rd) (hwr : ⟨st, 32⟩ ∈ s.wr) :
    WP isa code s fun s' =>
      (∀ k < 8, s'.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!) ∧
      CalleeSaved s s' ∧ Mem.AgreeL s.mem s'.mem s.wr := by
  let G : Ghost := ⟨H, msg, n, s⟩
  have hinp : G.inp = inp := hr4
  have hst : G.st = st := hr3
  have hwf : G.WF := ⟨hlen, hn, by rw [hinp]; exact hmsg, hK, by rw [hinp]; exact hrdm, hrdK⟩
  have hwrst : ∀ k, k + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 k) 16 := fun k hk =>
    ⟨_, List.mem_append_right _ hwr, Region.contains_offset _ _ _ _ hk (by norm_num)⟩
  apply WP.seq
  obtain ⟨t0, ht0⟩ := cmp_exec s
  refine WP.block_intro _ ht0 ?_
  refine WP.ite (s.getG .r5 == 0#64) rfl ?_ ?_
  · -- n = 0: nothing to do
    intro hb
    have h0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hb)
      simp only [hr5, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this; exact this
    subst h0
    refine WP.block_nil ⟨fun k hk => ?_, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩,
      Mem.AgreeL.refl _ _⟩
    rw [hashBlocks_eq H msg 0 hlen]; exact hHmem k hk
  · -- n > 0: set up, run the loop, store the hash value
    intro hb
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [hr5] at hb
      · exact h
    set s1 := cmpPost s with hs1
    have hF1 : Frame s s1 :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    apply WP.seq
    have hk256 : InRegions (s1.rd ++ s1.wr) (s1.labels kLabel + 256#64) 16 :=
      inRegions_of_mem (r := ⟨s.labels kLabel, 272⟩) hrdK (by norm_num) 256 16 (by norm_num)
    have hp0 := hwrst 0 (by decide)
    have hp1 := hwrst 16 (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hp0 hp1
    obtain ⟨t1, ht1⟩ := setup_exec s1 hk256 (by rw [show s1.getG .r3 = st from hr3]; exact hp0)
      (by rw [show s1.getG .r3 = st from hr3]; exact hp1)
    refine WP.block_intro _ ht1 ?_
    set s2 := setupPost s1 with hs2
    -- the loop invariant holds initially
    have f19 : s2.getV .v19 = lxv s.mem (s.labels kLabel + 256#64) := rfl
    have f18 : s2.getV .v18 = s.getV .v18 ^^^ s.getV .v18 := rfl
    have f16 : s2.getV .v16 = lxv s.mem st := by rw [← hr3]; rfl
    have f17 : s2.getV .v17 = lxv s.mem (st + 16#64) := by rw [← hr3]; rfl
    have g4 : s2.getG .r4 = inp := (show s2.getG .r4 = s.getG .r4 from rfl).trans hr4
    have g5 : s2.getG .r5 = ~~~(s.getG .r5) + 1#64 := rfl
    have hinv : LoopInv G 0 s2 := by
      refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simp only [s2, setupPost]
        exact ((((((((((((((hF1.setG _ rfl _).setG _ rfl _).setG _ rfl _).setG _ rfl _).setG _ rfl _).setG _ rfl
          _).setG _ rfl _).setG _ rfl _).setG _ rfl _).setG _ rfl _).setV _ rfl _).setV _ rfl _).setV _ rfl
          _).setV _ rfl _)
      · rw [f18, BitVec.xor_self]; rfl
      · -- the byte-swap mask
        rw [f19]
        have e : ∀ c, c < 4 → s.labels kLabel + 256#64 + BitVec.ofNat 64 (4 * c) =
            s.labels kLabel + BitVec.ofNat 64 (4 * (64 + c)) := fun c _ => by
          rw [show (256#64 : BitVec 64) = BitVec.ofNat 64 256 from rfl, add_ofNat_add]; congr 2; ring
        have e0 : s.labels kLabel + 256#64 = s.labels kLabel + BitVec.ofNat 64 (4 * (64 + 0)) := rfl
        have e1 : s.labels kLabel + 256#64 + 4 = _ := e 1 (by decide)
        have e2 : s.labels kLabel + 256#64 + 8 = _ := e 2 (by decide)
        have e3 : s.labels kLabel + 256#64 + 12 = _ := e 3 (by decide)
        rw [show lxv s.mem (s.labels kLabel + 256#64) = w4 (s.mem.readW (s.labels kLabel + 256#64) 32)
          (s.mem.readW (s.labels kLabel + 256#64 + 4) 32) (s.mem.readW (s.labels kLabel + 256#64 + 8) 32)
          (s.mem.readW (s.labels kLabel + 256#64 + 12) 32) from rfl, e3, e2, e1, e0,
          hK _ (by decide), hK _ (by decide), hK _ (by decide), hK _ (by decide), ← bswapVec_eq]
        rfl
      · rw [f16]
        rw [show lxv s.mem st = w4 (s.mem.readW st 32) (s.mem.readW (st + 4) 32) (s.mem.readW (st + 8) 32)
          (s.mem.readW (st + 12) 32) from rfl]
        have h0 := hHmem 0 (by decide); have h1 := hHmem 1 (by decide)
        have h2 := hHmem 2 (by decide); have h3 := hHmem 3 (by decide)
        simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
        rw [h0, show (st + 4) = st + 4#64 from rfl, h1, show (st + 8) = st + 8#64 from rfl, h2,
          show (st + 12) = st + 12#64 from rfl, h3]
        rfl
      · rw [f17]
        rw [show lxv s.mem (st + 16#64) = w4 (s.mem.readW (st + 16#64) 32) (s.mem.readW (st + 16#64 + 4) 32)
          (s.mem.readW (st + 16#64 + 8) 32) (s.mem.readW (st + 16#64 + 12) 32) from rfl]
        have h4 := hHmem 4 (by decide); have h5 := hHmem 5 (by decide)
        have h6 := hHmem 6 (by decide); have h7 := hHmem 7 (by decide)
        have e : ∀ c, st + 16#64 + BitVec.ofNat 64 c = st + BitVec.ofNat 64 (16 + c) := fun c => by
          rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
        have e4 : st + 16#64 + 4 = st + BitVec.ofNat 64 (4 * 5) := e 4
        have e8 : st + 16#64 + 8 = st + BitVec.ofNat 64 (4 * 6) := e 8
        have e12 : st + 16#64 + 12 = st + BitVec.ofNat 64 (4 * 7) := e 12
        have e0 : st + 16#64 = st + BitVec.ofNat 64 (4 * 4) := rfl
        rw [e4, e8, e12, e0, h4, h5, h6, h7]
        rfl
      · rw [g4, ← hinp]; simp
      · show s2.getG .r5 = -BitVec.ofNat 64 (n - 0)
        rw [g5, hr5, Nat.sub_zero, BitVec.neg_eq_not_add]
    apply WP.seq
    refine WP.mono (loop_ok G hwf _ hn0 hinv) ?_
    intro s3 h3
    -- the final store
    have hr3' : s3.getG .r3 = st := (h3.consts.frame.g .r3 rfl).trans hr3
    have hr7' : s3.getG .r7 = 16#64 := h3.consts.r7
    have hwr3 : s3.wr = s.wr := h3.consts.frame.wr
    have hq0 : InRegions s3.wr (s3.getG .r3) 16 := by
      rw [hwr3, hr3']
      exact ⟨_, hwr, by rw [region_contains_self]; decide⟩
    have hq1 : InRegions s3.wr (s3.getG .r3 + s3.getG .r7) 16 := by
      rw [hwr3, hr3', hr7']
      exact ⟨_, hwr, Region.contains_offset _ _ 16 16 (by decide) (by norm_num)⟩
    obtain ⟨t4, ht4⟩ := store_exec s3 hq0 hq1
    refine WP.block_intro _ ht4 ?_
    have hv0' := h3.v16; have hv1' := h3.v17
    have hm3 : s3.mem = s.mem := h3.consts.frame.mem
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · simp only [storePost, hr3', hr7', hv0', hv1', hm3, hv0, hv1, word_w4_0, word_w4_1, word_w4_2,
        word_w4_3]
      rw [read_state _ _ _ _ _ _ _ _ _ _ _ hk, hashBlocks_eq H msg n hlen]
      interval_cases k <;> rfl
    · have hF := h3.consts.frame
      show CalleeSaved s (storePost s3)
      refine ⟨fun r hr => ?_, fun r hr => ?_, fun m _ => ?_, ?_, ?_⟩
      · rw [storePost_getG]; exact hF.g r (by cases r <;> first | (cases hr; done) | rfl)
      · rw [storePost_getV]; exact hF.v r hr
      · rw [storePost_vsr, hF.vsr]
      · rw [storePost_cr1to7, hF.cr1to7]
      · rw [storePost_lr, hF.lr]
    · simp only [storePost, hr3', hr7', hm3]
      have c : ∀ j, j < 8 → (Region.mk st 32).Contains (st + BitVec.ofNat 64 (4 * j)) (32 / 8) := fun j hj =>
        Region.contains_offset _ _ _ _ (by omega) (by norm_num)
      have c0 : (Region.mk st 32).Contains st (32 / 8) := by rw [region_contains_self]; decide
      refine (((((((Mem.AgreeL.writeW (Mem.AgreeL.refl _ _) _ hwr _ _ c0).writeW _ hwr _ _ (c 1 (by decide))).writeW
        _ hwr _ _ (c 2 (by decide))).writeW _ hwr _ _ (c 3 (by decide))).writeW _ hwr _ _ (c 4 (by decide))).writeW
        _ hwr _ _ ?_).writeW _ hwr _ _ ?_).writeW _ hwr _ _ ?_
      · rw [BitVec.add_assoc]; exact c 5 (by decide)
      · rw [BitVec.add_assoc]; exact c 6 (by decide)
      · rw [BitVec.add_assoc]; exact c 7 (by decide)

end CC.Ppc.SHA256P8
