import FvModexp.Proofs.Amd64.Top.RunCDefs

set_option autoImplicit false

/-!
# `Run` (amd64): the compute calls — `IntPre` of `Bytes` on the result of `Mod`/`exp`, frames, budgets, values
(pure lemmas; twin of the arm64 `RunC2Lem2`/`RunC2Lem3`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- `RelD` reads only `RSP`, `R14`, `RBP`, `X15`, `fsBase`, `DF` and the memory of the state. -/
theorem RelD.congr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c p len cp : BitVec 64} {s : State} {ret k ks cst : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S T : State} (h : RelD R b L c p len cp s ret k ks cst Lk bk S)
    (hm : T.mem = S.mem) (h4 : T.regs 4 = S.regs 4) (h14 : T.regs 14 = S.regs 14) (h5 : T.regs 5 = S.regs 5)
    (hx : T.xmm 15 = S.xmm 15) (hfs : T.fsBase = S.fsBase) (hdf : T.df = S.df) :
    RelD R b L c p len cp s ret k ks cst Lk bk T := by
  unfold RelD at *
  rw [hm, h4, h14, h5, hx, hfs, hdf]; exact h

/-- A normalised nat of value `1` is the one-limb `1`. -/
theorem natVal_eq_one {m : Janus.Arm64.Memory} {p n : Nat} (hn : NatNorm m p n) (h : natVal m p n = 1) :
    n = 1 ∧ m.readLE p 8 = 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp at h
  · have := natVal_ge_norm m p n hn h0
    rw [h] at this
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge 1 n with h2 | h2
      · have : 2 ^ 64 ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · omega
    subst hn1
    refine ⟨rfl, ?_⟩
    have := natVal_succ m p 0
    simp only [natVal_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add] at this
    omega

theorem intV_eq (m : Janus.Arm64.Memory) (a : Nat) : RunIface.IntV m a = natAt m (a + 8) := by
  simp only [RunIface.IntV, natAt, show a + 8 + 8 = a + 16 by omega]

/-- A range apart from the runtime-owned ranges, the callee window, the header `z` and (if any) `z`'s old array is
outside the frame of an `IntPost`. -/
theorem out_post {rt : List (Nat × Nat)} {T : State} {M : Janus.Arm64.Memory} {stk above z a n : Nat}
    (hr : Outside a n rt) (hw : Apart a n ((T.regs 4).toNat - stk) (stk + above)) (hz : Apart a n z 32)
    (harr : 0 < M.readLE (z + 24) 8 → Apart a n (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8)) :
    Outside a n (rt ++ win T stk above ++ (z, z + 32) :: RunIface.arrW M z) := by
  unfold Apart at hw hz
  by_cases hc : 0 < M.readLE (z + 24) 8
  · have := harr hc; unfold Apart at this
    simp only [win, RunIface.arrW, if_pos hc, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨⟨hr, by omega⟩, by omega, by omega⟩
  · simp only [win, RunIface.arrW, if_neg hc, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨⟨hr, by omega⟩, by omega⟩

/-- `CallEnv` survives a callee that keeps the window accessible and the guard / TLS words, at the same `RSP`, `R14`,
`fsBase`, with a grown live set. -/
theorem callEnv_frame {R : RtInv} {L1 L2 : List (Nat × Nat)} {T t : State} {stk above : Nat}
    (hce : CallEnv R L1 T stk above) (h4 : t.regs 4 = T.regs 4) (h14 : t.regs 14 = T.regs 14)
    (hfs : t.fsBase = T.fsBase) (hacc : ∀ a n w, t.mem.accessible a n w = T.mem.accessible a n w)
    (hg : t.mem.readLE ((T.regs 14).toNat + 16) 8 = T.mem.readLE ((T.regs 14).toNat + 16) 8)
    (hf : t.mem.readLE (T.fsBase.toNat - 8) 8 = T.mem.readLE (T.fsBase.toNat - 8) 8)
    (hd : Extracted.program.DataLoaded t.mem) (hext : LiveExt R L1 L2) : CallEnv R L2 t stk above := by
  obtain ⟨hgd, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, hro, ⟨⟨hfb, hfr, hfg⟩, hfrt, hfw⟩⟩ := hce
  have hg3 := hgd.below
  have hg1 := hgd.noWrap
  have hg2 := hgd.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr hfg
  have hwr : ∀ r ∈ win T stk above, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by dsimp only; omega)
  unfold CallEnv TlsOK
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hd, ?_, ?_, ?_, ?_, hro, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  all_goals (try simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0, h4, h14, hfs, hacc, hg, hf])
  · exact hg1
  · exact hg2
  · exact hg3
  · exact hb'
  · exact ha
  · exact hw
  · exact hal
  · exact hout
  · exact hga
  · exact hgr
  · simpa only [win, h4] using hext.liveSep hLs hwr
  · exact hfb
  · exact hfr
  · exact hfg
  · exact hfrt
  · exact hfw

open RunIface in
/-- `IntPre` of `x.Bytes()` on the result `z` of `Mod` / `exp` (same entry `RSP`, `R14`, `fsBase`), from the callee's
`IntPre` facts about `z` and its `IntPost`. -/
theorem intPre_one {R : RtInv} {b2 B2 : Nat} {L1 L2 : List (Nat × Nat)} {T : State} {M M1 : Janus.Arm64.Memory}
    {stk above z : Nat}
    (hTm : T.mem = M) (hce : CallEnv R L1 T stk above) (hgl : Globals R M (win T stk above)) (hsv : Serves R)
    (hok0 : IntOK M R L1 z) (hzw : Outside z 32 (win T stk above)) (hzg : Apart z 32 ((T.regs 14).toNat + 16) 8)
    (hzf : Apart z 32 (T.fsBase.toNat - 8) 8)
    (harr : 0 < M.readLE (z + 24) 8 →
      Outside (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) (win T stk above) ∧
      Apart (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) ((T.regs 14).toNat + 16) 8 ∧
      Apart (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) (T.fsBase.toNat - 8) 8 ∧
      Apart gA 32 (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8))
    (hgz : Apart gA 32 z 32)
    (hMF1 : MemFrame M M1 (R.rt ++ win T stk above ++ (z, z + 32) :: arrW M z))
    (hreg : M1.regions = M.regions) (hext : LiveExt R L1 L2)
    (hinv2 : R.inv b2 L2 (T.regs 14).toNat (view R.rt L2 M1)) (hok : IntOK M1 R L2 z)
    (hor : 0 < M1.readLE (z + 24) 8 →
      (M1.readLE (z + 8) 8 = M.readLE (z + 8) 8 ∧ M1.readLE (z + 24) 8 = M.readLE (z + 24) 8) ∨
      (InRanges (M1.readLE (z + 8) 8) (8 * M1.readLE (z + 24) 8) R.rt ∧
        ApartAll (M1.readLE (z + 8) 8) (8 * M1.readLE (z + 24) 8) L1))
    (hB : B2 ≤ b2) :
    ∀ t : State, t.regs 4 = T.regs 4 → t.mem = M1 → t.regs 14 = T.regs 14 → t.fsBase = T.fsBase →
      IntPre R b2 B2 L2 stk above [z] t := by
  intro t hsp hm h14 hfs
  have hce0 := hce
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨⟨hfb, hfr, hfg⟩, hfrt, hfw⟩⟩ := hce
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr hfg
  rw [hTm] at hg2 hg3 hw hd hfr hfg
  obtain ⟨e0, e1, e2, e3, a1, a2, a3, hacc, hrt, hwg, hwbA, hwbR, hwbW⟩ := hgl
  have hacc1 : ∀ a n w, M1.accessible a n w = M.accessible a n w := hMF1.accessible
  have hgM : M1.readLE ((T.regs 14).toNat + 16) 8 = M.readLE ((T.regs 14).toNat + 16) 8 :=
    hMF1.readLE _ _ (out_post hgr hga hzg.symm fun hc => (harr hc).2.1.symm)
  have hfM : M1.readLE (T.fsBase.toNat - 8) 8 = M.readLE (T.fsBase.toNat - 8) 8 :=
    hMF1.readLE _ _ (out_post hfrt hfw hzf.symm fun hc => (harr hc).2.2.1.symm)
  have hwr : ∀ r ∈ win T stk above, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by dsimp only; omega)
  have hwg' := hwg
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwg'
  have hG : ∀ k, k + 8 ≤ 32 → M1.readLE (gA + k) 8 = M.readLE (gA + k) 8 := fun k hk =>
    hMF1.readLE _ _ (out_post (hrt.of_sub (by omega) (by omega)) (by unfold Apart; omega)
      (by unfold Apart at hgz ⊢; omega) fun hc => by have := (harr hc).2.2.2; unfold Apart at this ⊢; omega)
  have hce' : CallEnv R L2 t stk above :=
    callEnv_frame hce0 hsp h14 hfs
      (by rw [hm, hTm]; exact hacc1) (by rw [hm, hTm]; exact hgM) (by rw [hm, hTm]; exact hfM) ?dl hext
  unfold IntPre
  rw [hm, h14, hfs]
  refine ⟨hce', hsv, ⟨?g1, ?g2, ?g3, ?g4, a1, a2, a3, by rw [hacc1]; exact hacc, hrt, by rw [show win t stk above = win T stk above by simp only [win, hsp]]; exact hwg,
      by rw [hacc1]; exact hwbA, hwbR, by rw [show win t stk above = win T stk above by simp only [win, hsp]]; exact hwbW⟩,
    hB, hinv2, ?ints, List.pairwise_singleton _ _⟩
  case dl =>
    rw [hm]
    refine dataLoaded_frame64 hd hreg hro (by rw [List.append_assoc] at hMF1; exact hMF1) fun r hr hlt => ?_
    simp only [win, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨-, -, -, hza, -, hlv, -⟩ := hok0
    rcases hr with rfl | rfl | hr
    · exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by dsimp only; omega)
    · simpa using hza
    · simp only [RunIface.arrW] at hr
      split at hr
      · rename_i hc; simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨-, -, h3, -⟩ := hlv hc
        simpa using h3
      · simp at hr
  case g1 => rw [a1, hG 8 (by omega), ← a1]; exact e0
  case g2 => rw [a2, hG 16 (by omega), ← a2]; exact e1
  case g3 => rw [a3, hG 24 (by omega), ← a3]; exact e2
  case g4 => exact (hG 0 (by omega)).trans e3
  case ints =>
    intro a ha
    simp only [List.mem_singleton] at ha; subst ha
    refine ⟨hok, by simpa [win, hsp] using hzw, fun hc => ?_, hzg, fun hc => ?_, hzf, fun hc => ?_⟩
    · rcases hor hc with ⟨hp, hcc⟩ | ⟨hin, -⟩
      · rw [hp, hcc]; simpa [win, hsp] using (harr (by rw [← hcc]; exact hc)).1
      · have := InRanges.apart hin (hout : Outside _ _ R.rt)
        simp only [win, hsp, Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at this; omega
    · rcases hor hc with ⟨hp, hcc⟩ | ⟨hin, -⟩
      · rw [hp, hcc]; exact (harr (by rw [← hcc]; exact hc)).2.1
      · exact (InRanges.apart hin hgr).symm
    · rcases hor hc with ⟨hp, hcc⟩ | ⟨hin, -⟩
      · rw [hp, hcc]; exact (harr (by rw [← hcc]; exact hc)).2.2.1
      · exact (InRanges.apart hin hfrt).symm

open RunIface in
/-- After `Mod`/`exp` on the first `*Int` `z` of the call: the callee's post, and the `IntPre` of `z.Bytes()` at the
same entry `RSP`/`R14`/`fsBase`. -/
theorem afterInt {R : RtInv} {b1 B B2 : Nat} {L1 : List (Nat × Nat)} {stk above z v : Nat} {ys : List Nat}
    {sc s' : State} {sp0 g fs : BitVec 64} {M : Janus.Arm64.Memory}
    (hIP : ∀ t : State, t.regs 4 = sp0 → t.mem = M → t.regs 14 = g → t.fsBase = fs →
      IntPre R b1 B L1 stk above (z :: ys) t)
    (hpost : IntPost R b1 B L1 stk above z v sc s') (e1 : sc.regs 4 = sp0) (e2 : sc.mem = M) (e3 : sc.regs 14 = g)
    (e4 : sc.fsBase = fs)
    (hreg : s'.mem.regions = sc.mem.regions) (hgz : Apart gA 32 z 32)
    (hga : 0 < sc.mem.readLE (z + 24) 8 →
      Apart gA 32 (sc.mem.readLE (z + 8) 8) (8 * sc.mem.readLE (z + 24) 8))
    (hBB : B + B2 ≤ b1) :
    ∃ (L2 : List (Nat × Nat)) (b2 : Nat), LiveExt R L1 L2 ∧ b1 - B ≤ b2 ∧ IntV s'.mem z = v ∧
      R.inv b2 L2 (sc.regs 14).toNat (view R.rt L2 s'.mem) ∧ IntOK s'.mem R L2 z ∧
      MemFrame sc.mem s'.mem (R.rt ++ win sc stk above ++ (z, z + 32) :: arrW sc.mem z) ∧
      LiveFrame sc.mem s'.mem L1 ((z, z + 32) :: arrW sc.mem z) ∧
      (∀ t : State, t.regs 4 = sc.regs 4 → t.mem = s'.mem → t.regs 14 = sc.regs 14 → t.fsBase = sc.fsBase →
        IntPre R b2 B2 L2 stk above [z] t) := by
  obtain ⟨hv, L2, b2, hext, hb2, hinv2, hok, hor, hMF, hLF⟩ := hpost
  obtain ⟨hce, hsv, hgl, hB, -, hints, -⟩ := hIP sc e1 e2 e3 e4
  obtain ⟨hok0, hzw, harw, hzg, harg, hzf, harf⟩ := hints z (List.mem_cons_self ..)
  have hgl' : Globals R sc.mem (win sc stk above) := hgl
  refine ⟨L2, b2, hext, hb2, hv, hinv2, hok, hMF, hLF,
    intPre_one rfl hce hgl' hsv hok0 hzw hzg hzf (fun hc => ⟨harw hc, harg hc, harf hc, hga hc⟩) hgz hMF hreg hext
      hinv2 hok hor (by omega)⟩

open RunIface in
/-- An operand's word count is at most `⌈len / 8⌉` of its byte length. -/
theorem lenW_op {R : RtInv} {M : Janus.Arm64.Memory} {s : State} {p len : BitVec 64} {L L1 : List (Nat × Nat)} {j : Nat}
    (h : OpDone R M s p len L L1 j) (hj : j < 3) : lenW M (opAt s j) ≤ opW s p len j := by
  obtain ⟨-, hv, hn, -⟩ := h
  simp only [natAt, show opAt s j + 8 + 8 = opAt s j + 16 by omega] at hv
  have hlt := padBE_lt s.mem p.toNat len.toNat (96 + opStart s p len j) (opLen s p len j)
  have hol : opLen s p len j = hdrV s p len j := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp only [opLen, ↓reduceIte] <;> rfl
  have h256 : (256 : Nat) ^ hdrV s p len j = 2 ^ (8 * hdrV s p len j) := by rw [Nat.pow_mul]
  have hlt' : natVal M (M.readLE (opAt s j + 8) 8) (M.readLE (opAt s j + 16) 8) < 2 ^ (8 * hdrV s p len j) := by
    rw [hv, ← h256, ← hol]; exact hlt
  exact len_le_of_lt M _ _ _ hn hlt'

/-- `lenW_op` at operand 0's literal address (unifying `opAt s ?j` with a literal costs ≈ 16 s per use). -/
theorem lenW_op0 {R : RtInv} {M : Janus.Arm64.Memory} {s : State} {p len : BitVec 64} {L L1 : List (Nat × Nat)}
    (h : OpDone R M s p len L L1 0) : RunIface.lenW M ((s.regs 4).toNat - 136) ≤ opW s p len 0 := by
  have := lenW_op h (by omega)
  rwa [show opAt s 0 = (s.regs 4).toNat - 136 by simp only [opAt]; omega] at this

/-- `lenW_op` at operand 1's literal address (unifying `opAt s ?j` with a literal costs ≈ 16 s per use). -/
theorem lenW_op1 {R : RtInv} {M : Janus.Arm64.Memory} {s : State} {p len : BitVec 64} {L L1 : List (Nat × Nat)}
    (h : OpDone R M s p len L L1 1) : RunIface.lenW M ((s.regs 4).toNat - 168) ≤ opW s p len 1 := by
  have := lenW_op h (by omega)
  rwa [show opAt s 1 = (s.regs 4).toNat - 168 by simp only [opAt]; omega] at this

/-- `lenW_op` at operand 2's literal address (unifying `opAt s ?j` with a literal costs ≈ 16 s per use). -/
theorem lenW_op2 {R : RtInv} {M : Janus.Arm64.Memory} {s : State} {p len : BitVec 64} {L L1 : List (Nat × Nat)}
    (h : OpDone R M s p len L L1 2) : RunIface.lenW M ((s.regs 4).toNat - 200) ≤ opW s p len 2 := by
  have := lenW_op h (by omega)
  rwa [show opAt s 2 = (s.regs 4).toNat - 200 by simp only [opAt]; omega] at this

open RunIface in
theorem budget_mod {b b1 X w lw0 lw2 lb E A : Nat} (h0 : lw0 ≤ w) (h2 : lw2 ≤ w) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hB : X + (ModBudget w + E + BytesBudget maxW) + A ≤ b) :
    ModBudget (max lw0 lw2) + BytesBudget lb ≤ b1 := by
  have e1 : ModBudget (max lw0 lw2) ≤ ModBudget w := by
    unfold ModBudget opCost allocCost; omega
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

open RunIface in
/-- The two calls keep everything outside `R.rt` and `Run`'s window `W` (`z`'s header lies in `Run`'s frame, its old
array is a runtime object). -/
theorem frame_TV {R : RtInv} {M M1 M2 : Janus.Arm64.Memory} {sc t : State} {e W stkM aboveM z : Nat}
    (hW : 616 + stkM ≤ W) (hab : aboveM ≤ 144) (heW : W ≤ e)
    (hsc : (sc.regs 4).toNat = e - 616) (ht : (t.regs 4).toNat = e - 616) (hz1 : e - W ≤ z) (hz2 : z + 32 ≤ e + 40)
    (harr : 0 < M.readLE (z + 24) 8 → InRanges (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) R.rt)
    (h1 : MemFrame M M1 (R.rt ++ win sc stkM aboveM ++ (z, z + 32) :: arrW M z))
    (h2 : MemFrame M1 M2 (R.rt ++ win t stkM aboveM)) :
    MemFrame M M2 (R.rt ++ [(e - W, e + 40)]) :=
  h1.trans h2 fun a n h => by
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h
    obtain ⟨hr, hw⟩ := h
    refine ⟨out_post hr (by unfold Apart; omega) (by unfold Apart; omega) fun hc => ?_, ?_⟩
    · have := InRanges.apart (harr hc) hr; unfold Apart at this ⊢; omega
    · simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hr, by omega⟩

open RunIface in
/-- A slot of `Run`'s frame that neither callee writes: outside `R.rt`, above the callee windows, apart from `z`'s
header. -/
theorem slot_TV {R : RtInv} {M M1 M2 : Janus.Arm64.Memory} {sc t : State} {stkM aboveM z a n q : Nat}
    (ht : (t.regs 4).toNat = q) (hq : (sc.regs 4).toNat = q) (hr : Outside a n R.rt)
    (hw : q + aboveM ≤ a)
    (hz : a + n ≤ z ∨ z + 32 ≤ a)
    (harr : 0 < M.readLE (z + 24) 8 → InRanges (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) R.rt)
    (h1 : MemFrame M M1 (R.rt ++ win sc stkM aboveM ++ (z, z + 32) :: arrW M z))
    (h2 : MemFrame M1 M2 (R.rt ++ win t stkM aboveM)) :
    M2.readLE a n = M.readLE a n := by
  have hwA : Outside a n (win sc stkM aboveM) := by
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hwA' : Outside a n (win t stkM aboveM) := by
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  rw [h2.readLE a n (by rw [Janus.outside_append]; exact ⟨hr, hwA'⟩), h1.readLE a n ?o1]
  case o1 =>
    rw [Janus.outside_append, Janus.outside_append]
    refine ⟨⟨hr, hwA⟩, ?_⟩
    simp only [Janus.outside_cons]
    refine ⟨hz, ?_⟩
    simp only [arrW]
    generalize M.readLE (z + 24) 8 = cap at harr ⊢
    generalize M.readLE (z + 8) 8 = ptr at harr ⊢
    rcases Nat.eq_zero_or_pos cap with h0 | hc
    · subst h0; simp only [Nat.lt_irrefl, if_false, Janus.outside_nil]
    · have := InRanges.apart (harr hc) hr; unfold Apart at this
      simp only [hc, if_true, Janus.outside_cons, Janus.outside_nil, and_true]; omega

open RunIface in
/-- The objects of the caller's live set `L` are unchanged by the two calls. -/
theorem liveFrame_TV {R : RtInv} {M M1 M2 : Janus.Arm64.Memory} {L L1 L2 : List (Nat × Nat)} {e W z : Nat}
    (hext1 : LiveExt R L L1) (hext2 : LiveExt R L1 L2) (hLs : LiveSep L [(e - W, e + 40)])
    (hz1 : e - W ≤ z) (hz2 : z + 32 ≤ e + 40)
    (harr : 0 < M.readLE (z + 24) 8 → ApartAll (M.readLE (z + 8) 8) (8 * M.readLE (z + 24) 8) L)
    (h1 : LiveFrame M M1 L1 ((z, z + 32) :: arrW M z)) (h2 : LiveFrame M1 M2 L2 []) :
    LiveFrame M M2 L [] :=
  ⟨fun a n hin _ => by
    rw [h2.readLE a n (hext2.inRanges_old (hext1.inRanges_old hin)) trivial]
    refine h1.readLE a n (hext1.inRanges_old hin) ?_
    obtain ⟨r, hr, i1, i2⟩ := hin
    have hw := hLs r hr
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hw
    simp only [arrW]
    generalize M.readLE (z + 24) 8 = cap at harr ⊢
    generalize M.readLE (z + 8) 8 = ptr at harr ⊢
    rcases Nat.eq_zero_or_pos cap with h0 | hc
    · subst h0; simp only [Nat.lt_irrefl, if_false, Janus.outside_cons, Janus.outside_nil, and_true]; omega
    · have := harr hc r hr; unfold Apart at this
      simp only [hc, if_true, Janus.outside_cons, Janus.outside_nil, and_true]; omega⟩

open RunIface in
/-- The budget of `Mod` + `Bytes` fits the compute allowance `callB`. -/
theorem budget_c2m {b b1 b2 b3 X w lw0 lw2 lb E : Nat} (h0 : lw0 ≤ w) (h2 : lw2 ≤ w) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hb2 : b1 - ModBudget (max lw0 lw2) ≤ b2) (hb3 : b2 - BytesBudget lb ≤ b3) :
    b - (X + (ModBudget w + E + BytesBudget maxW)) ≤ b3 := by
  have e1 : ModBudget (max lw0 lw2) ≤ ModBudget w := by
    unfold ModBudget opCost allocCost; omega
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

open RunIface in
/-- The budget of `exp` + `Bytes` fits the compute allowance `callB`. -/
theorem budget_c2e {b b1 b2 b3 X w yW lw0 lw1 lw2 lb M : Nat} (h0 : lw0 ≤ w) (h1 : lw1 ≤ w) (h2 : lw2 ≤ w)
    (hy : lw1 ≤ yW) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hb2 : b1 - ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ b2) (hb3 : b2 - BytesBudget lb ≤ b3) :
    b - (X + (M + ExpBudget w yW + BytesBudget maxW)) ≤ b3 := by
  have e1 : ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ ExpBudget w yW := by
    unfold ExpBudget opCost allocCost
    have : max (max lw0 lw1) lw2 ≤ w := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul_left _ (by omega))
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

open RunIface in
/-- The `Mod`/`exp` budget fits what `Run` has left after the operands (the `Bytes` allowance kept apart). -/
theorem budget_c2e0 {b b1 X w yW lw0 lw1 lw2 lb M A : Nat} (h0 : lw0 ≤ w) (h1 : lw1 ≤ w) (h2 : lw2 ≤ w)
    (hy : lw1 ≤ yW) (hl : lb ≤ maxW)
    (hb : b - X ≤ b1) (hB : X + (M + ExpBudget w yW + BytesBudget maxW) + A ≤ b) :
    ExpBudget (max (max lw0 lw1) lw2) lw1 + BytesBudget lb ≤ b1 := by
  have e1 : ExpBudget (max (max lw0 lw1) lw2) lw1 ≤ ExpBudget w yW := by
    unfold ExpBudget opCost allocCost
    have : max (max lw0 lw1) lw2 ≤ w := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul_left _ (by omega))
  have e2 : BytesBudget lb ≤ BytesBudget maxW := by
    unfold BytesBudget allocCost; omega
  omega

/-- The value `Run` computes, as `resV`. -/
theorem resV_eq (s : State) (p len : BitVec 64) (h2 : 0 < opV s p len 2) :
    resV s p len = opV s p len 0 ^ opV s p len 1 % opV s p len 2 := by
  unfold resV; rw [if_neg (by omega)]

/-- A value below the modulus fits `modLen` bytes. -/
theorem lt_modLen (s : State) (p len : BitVec 64) {v : Nat} (h : v < opV s p len 2) : v < 256 ^ hdrV s p len 2 := by
  have := padBE_lt s.mem p.toNat len.toNat (96 + opStart s p len 2) (opLen s p len 2)
  simp only [opV, opLen, show (2 : Nat) = 0 ↔ False by decide, show (2 : Nat) = 1 ↔ False by decide,
    if_false] at h this
  omega

end FvModexp.Amd64.Run
