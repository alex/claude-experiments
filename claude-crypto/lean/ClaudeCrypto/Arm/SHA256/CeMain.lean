import ClaudeCrypto.Arm.SHA256.CeBlock

/-!
# Correctness of `cc_sha256_blocks_arm`

The main theorem, `correct`, states that running the function body from any
state satisfying the function's preconditions

* terminates without faulting — in particular it only reads the message, the
  round-constant table and the hash value, and only writes the hash value
  (memory safety);
* leaves FIPS 180-4's `hashBlocks H msg` in the hash-value buffer;
* preserves every register the AAPCS64 calling convention requires a function
  to preserve (`X19`–`X30`, `SP`, `D8`–`D15`); and
* leaves all memory outside the writable regions unchanged.
-/

namespace CC.Arm.SHA256Ce

open CC.Spec.SHA256

theorem hashBlocks_eq (H : List Word) (msg : List (BitVec 8)) (n : Nat) (hl : msg.length = 64 * n) :
    hashBlocks H msg = stateAfter H msg n := blocks_foldl H msg n hl

/-- Reading back word `k` of the 32-byte hash value written by `st1 {v0.4s, v1.4s}`. -/
theorem read_state (m : Mem) (st : Addr) (a0 a1 a2 a3 e0 e1 e2 e3 : Word) (k : Nat) (hk : k < 8) :
    ((m.writeW st (vec4 a0 a1 a2 a3)).writeW (st + 16#64) (vec4 e0 e1 e2 e3)).readW
        (st + BitVec.ofNat 64 (4 * k)) 32 = [a0, a1, a2, a3, e0, e1, e2, e3][k]! := by
  by_cases h4 : k < 4
  · rw [Mem.readW_writeW_sep _ _ _ _ _ (by
      rw [show st + 16#64 = st + BitVec.ofNat 64 16 from rfl, sep_add_add]
      unfold Mem.Sep
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      interval_cases k <;> decide)]
    rw [readW_writeW_vec4 _ _ _ _ _ _ _ h4]
    interval_cases k <;> simp [elem_vec4_0, elem_vec4_1, elem_vec4_2, elem_vec4_3]
  · have e : st + BitVec.ofNat 64 (4 * k) = st + 16#64 + BitVec.ofNat 64 (4 * (k - 4)) := by
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; congr 2; omega
    rw [e, readW_writeW_vec4 _ _ _ _ _ _ _ (by omega)]
    interval_cases k <;> simp [elem_vec4_0, elem_vec4_1, elem_vec4_2, elem_vec4_3]

set_option maxHeartbeats 2000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_sha256_blocks_arm`.**

`s` is the machine state on entry: `x0` points to the hash value `H`
(eight 32-bit words, native byte order), `x1` to the message `msg`
(`64 * n` bytes), and `x2 = n`; the program's round-constant table is at
`s.labels kLabel`.  The code may read the message and the table and read and
write the hash value (`s.rd`, `s.wr` may contain further regions). -/
theorem correct (s : State) (H : List Word) (msg : List (BitVec 8)) (n : Nat) (st inp : Addr)
    (hlen : msg.length = 64 * n) (hn : 64 * n < 2 ^ 64)
    (hx0 : s.x.x0 = st) (hx1 : s.x.x1 = inp) (hx2 : s.x.x2 = BitVec.ofNat 64 n)
    (hHmem : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (hmsg : ∀ i < 64 * n, s.mem (inp + BitVec.ofNat 64 i) = msg[i]!)
    (hK : ∀ i < 64, s.mem.readW (s.labels kLabel + BitVec.ofNat 64 (4 * i)) 32 = K[i]!)
    (hrdm : ⟨inp, 64 * n⟩ ∈ s.rd) (hrdK : ⟨s.labels kLabel, 256⟩ ∈ s.rd) (hwr : ⟨st, 32⟩ ∈ s.wr) :
    WP isa code s fun s' =>
      (∀ k < 8, s'.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (hashBlocks H msg)[k]!) ∧
      CalleeSaved s s' ∧ Mem.AgreeL s.mem s'.mem s.wr := by
  let G : Ghost := ⟨H, msg, n, s⟩
  have hinp : G.inp = inp := hx1
  have hst : G.st = st := hx0
  have hwf : G.WF := ⟨hlen, hn, by rw [hinp]; exact hmsg, hK, by rw [hinp]; exact hrdm, hrdK⟩
  have hwrst : ∀ k, k + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 k) 16 := fun k hk =>
    ⟨_, List.mem_append_right _ hwr, Region.contains_offset _ _ _ _ hk (by norm_num)⟩
  refine WP.ite (s.getX .x2 == 0) rfl ?_ ?_
  · -- n = 0: nothing to do
    intro hb
    have h0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hb)
      simp only [State.getX, XRegs.get, hx2, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this; exact this
    subst h0
    refine WP.block_nil ⟨fun k hk => ?_, ?_, Mem.AgreeL.refl _ _⟩
    · rw [hashBlocks_eq H msg 0 hlen]; exact hHmem k hk
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
  · -- n > 0: load the hash value, run the loop, store the hash value
    intro hb
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [State.getX, XRegs.get, hx2] at hb
      · exact h
    apply WP.seq
    have hp0 := hwrst 0 (by decide)
    have hp1 := hwrst 16 (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hp0 hp1
    obtain ⟨t1, ht1⟩ := loadState_exec s (by rw [State.getX, XRegs.get, hx0]; exact hp0)
      (by rw [State.getX, XRegs.get, hx0]; exact hp1)
    refine WP.block_intro _ ht1 ?_
    -- the loop invariant holds initially
    have hH4 : ∀ k, k < 8 → s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]! := hHmem
    have hinv : LoopInv G 0 (loadStatePost s) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
      · unfold loadStatePost
        exact (((Frame.refl s).setV _ (by decide) _).setV _ (by decide) _).setX _ (by simp) _
      · refine (show (loadStatePost s).getV .v0 = s.mem.readW (s.getX .x0) 128 from rfl).trans ?_
        rw [State.getX, XRegs.get, hx0, readW_128]
        have h1 := hH4 1 (by decide); have h2 := hH4 2 (by decide); have h3 := hH4 3 (by decide)
        have h0 := hH4 0 (by decide)
        simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
        rw [h0, h1, h2, h3]; rfl
      · refine (show (loadStatePost s).getV .v1 = s.mem.readW (s.getX .x0 + 16#64) 128 from rfl).trans ?_
        rw [State.getX, XRegs.get, hx0, readW_128]
        have e : ∀ c, st + 16#64 + BitVec.ofNat 64 c = st + BitVec.ofNat 64 (16 + c) := fun c => by
          rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
        have e4 := e 4; have e8 := e 8; have e12 := e 12
        simp only [Nat.reduceAdd] at e4 e8 e12
        rw [e4, e8, e12]
        have h4 := hH4 4 (by decide); have h5 := hH4 5 (by decide); have h6 := hH4 6 (by decide)
        have h7 := hH4 7 (by decide)
        simp only [Nat.reduceMul] at h4 h5 h6 h7
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, h4, h5, h6, h7]; rfl
      · refine (show (loadStatePost s).getX .x1 = s.getX .x1 from rfl).trans ?_
        show s.getX .x1 = s.getX .x1 + BitVec.ofNat 64 (64 * 0)
        simp
      · refine (show (loadStatePost s).getX .x2 = s.getX .x2 from rfl).trans ?_
        show s.x.x2 = BitVec.ofNat 64 (n - 0)
        rw [Nat.sub_zero]; exact hx2
    apply WP.seq
    refine WP.mono (loop_ok G hwf _ hn0 hinv) ?_
    intro s3 h3
    -- the final store
    have hx0' : s3.getX .x0 = st := (h3.frame.x .x0 (by decide) (by decide) (by decide)).trans hx0
    have hwr3 : s3.wr = s.wr := h3.frame.wr
    have hq0 : InRegions s3.wr (s3.getX .x0) 16 := by
      rw [hwr3, hx0']
      exact ⟨_, hwr, by rw [region_contains_self]; decide⟩
    have hq1 : InRegions s3.wr (s3.getX .x0 + 16#64) 16 := by
      rw [hwr3, hx0']
      exact ⟨_, hwr, Region.contains_offset _ _ 16 16 (by decide) (by norm_num)⟩
    obtain ⟨t4, ht4⟩ := storeState_exec s3 hq0 hq1
    refine WP.block_intro _ ht4 ?_
    have hv0 := h3.v0; have hv1 := h3.v1
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · simp only [storeStatePost, hx0', hv0, hv1, h3.frame.mem]
      rw [abcd, efgh, read_state _ _ _ _ _ _ _ _ _ _ _ hk, hashBlocks_eq H msg n hlen]
      simp only [initVars]
      interval_cases k <;> rfl
    · have hx : ∀ r : XReg, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → (storeStatePost s3).x.get r = s.x.get r :=
        fun r h1 h2 h3' => h3.frame.x r h1 h2 h3'
      have hv : ∀ r : VReg, r ∉ touched → (storeStatePost s3).v.get r = s.v.get r :=
        fun r hr => h3.frame.v r hr
      exact ⟨hx .x19 (by decide) (by decide) (by decide), hx .x20 (by decide) (by decide) (by decide),
        hx .x21 (by decide) (by decide) (by decide), hx .x22 (by decide) (by decide) (by decide),
        hx .x23 (by decide) (by decide) (by decide), hx .x24 (by decide) (by decide) (by decide),
        hx .x25 (by decide) (by decide) (by decide), hx .x26 (by decide) (by decide) (by decide),
        hx .x27 (by decide) (by decide) (by decide), hx .x28 (by decide) (by decide) (by decide),
        hx .x29 (by decide) (by decide) (by decide), hx .x30 (by decide) (by decide) (by decide),
        h3.frame.sp,
        congrArg _ (hv .v8 (by decide)), congrArg _ (hv .v9 (by decide)),
        congrArg _ (hv .v10 (by decide)), congrArg _ (hv .v11 (by decide)),
        congrArg _ (hv .v12 (by decide)), congrArg _ (hv .v13 (by decide)),
        congrArg _ (hv .v14 (by decide)), congrArg _ (hv .v15 (by decide))⟩
    · simp only [storeStatePost, hx0', h3.frame.mem]
      refine (Mem.AgreeL.writeW (Mem.AgreeL.refl _ _) _ hwr _ _ ?_).writeW _ hwr _ _ ?_
      · rw [region_contains_self]; decide
      · exact Region.contains_offset _ _ 16 16 (by decide) (by norm_num)

end CC.Arm.SHA256Ce
