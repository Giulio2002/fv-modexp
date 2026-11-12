import FvModexp.Proofs.Amd64.Top.RunCDefs

/-!
# `Run` (amd64): the compute calls — callee preconditions, frames, budgets (pure lemmas; twin of the arm64
`RunC2Lem`/`RunC2Lem2`/`RunC2Lem3`)

`Run` calls `(*Int).Mod` / `(*Int).exp` on its stack `big.Int`s (`base` at `e - 136`, `exp` at `e - 168`, `mod` at
`e - 200`, `e` = `Run`'s entry `RSP`); the callee's entry `RSP` is `e - 616` (the `CALL` pushed the return address there),
then `(*Int).Bytes` on the result. The callee window `[e - 616 - stkM, e - 616 + aboveM)` must lie in `Run`'s window
`[e - W, e + 40)` (`616 + stkM ≤ W`) and below `modLen`'s slot `e - 472` (`aboveM ≤ 144`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem outside_of_inRanges {a n : Nat} {L ws : List (Nat × Nat)} (h : InRanges a n L) (hs : LiveSep L ws) :
    Outside a n ws := by
  obtain ⟨r, hr, h1, h2⟩ := h
  exact (hs r hr).of_sub h1 (by omega)

/-- An object of the extended live set is apart from a word that is apart from `L` and outside `R.rt`. -/
theorem apart_guard {R : RtInv} {L L1 : List (Nat × Nat)} {g a n : Nat} (hext : LiveExt R L L1)
    (hgL : ApartAll g 8 L) (hgr : Outside g 8 R.rt) (h : InRanges a n L1) : Apart a n g 8 := by
  obtain ⟨ns, rfl, hns, -⟩ := hext
  obtain ⟨r, hr, h1, h2⟩ := h
  rcases List.mem_append.1 hr with hr | hr
  · have := hgL r hr; unfold Apart at this ⊢; omega
  · have := InRanges.apart (hns r hr).1 hgr; unfold Apart at this ⊢; omega

/-- The live set of the operand phase is outside `Run`'s whole window `W`. -/
theorem liveSep_W {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {W : Nat} (hext : LiveExt R L L1)
    (hLs : LiveSep L (win s W 40)) (hout : Outside ((s.regs 4).toNat - W) (W + 40) R.rt) (hW : W ≤ (s.regs 4).toNat) :
    LiveSep L1 (win s W 40) :=
  hext.liveSep hLs fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by dsimp only; omega)

/-- The callee's `CallEnv` at `Run`'s call sites (entry `RSP = e - 616`), from `Run`'s with window `W ≥ 616 + stkM`. -/
theorem callEnv_c {R : RtInv} {L L1 : List (Nat × Nat)} {s T : State} {M : Janus.Arm64.Memory} {W stkM aboveM : Nat}
    (hT : (T.regs 4).toNat = (s.regs 4).toNat - 616) (hTm : T.mem = M) (hT14 : T.regs 14 = s.regs 14)
    (hTfs : T.fsBase = s.fsBase)
    (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (ha8 : 8 ≤ aboveM)
    (hdS : Extracted.program.DataLoaded M) (hext : LiveExt R L L1)
    (hMF : MemFrame s.mem M (R.rt ++ win s 4800 40)) :
    CallEnv R L1 T stkM aboveM := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨⟨hfb, hfr, hfg⟩, hfrt, hfw⟩⟩ := henvW
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr hfg
  have hLs1 := liveSep_W hext hLs hout hb'
  unfold Apart at hga hfw
  have hgM : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, by omega⟩)
  have hfM : M.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 :=
    hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hfrt, by omega⟩)
  unfold CallEnv TlsOK
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  all_goals (try simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0, hT, hTm, hT14, hTfs])
  · exact hg1
  · rw [hMF.accessible]; exact hg2
  · rw [hgM]; omega
  · omega
  · omega
  · rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact hdS
  · exact hout.of_sub (by omega) (by omega)
  · unfold Apart; omega
  · exact hgr
  · intro r hr
    have := hLs1 r hr
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
    omega
  · exact hfb
  · rw [hMF.accessible]; exact hfr
  · rw [hfM]; exact hfg
  · exact hfrt
  · unfold Apart; omega

/-- `Globals` at the callee's state, from `Run`'s. -/
theorem globals_c {R : RtInv} {s T : State} {M : Janus.Arm64.Memory} {W stkM aboveM : Nat}
    (hT : (T.regs 4).toNat = (s.regs 4).toNat - 616) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144)
    (hsW : W ≤ (s.regs 4).toNat)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hMF : MemFrame s.mem M (R.rt ++ win s 4800 40)) :
    RunIface.Globals R M (win T stkM aboveM) := by
  obtain ⟨h1, h2, h3, h4, e1, e2, e3, hacc, hrt, hw, hwa, hwr, hww⟩ := hglob
  have hw' := hw
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hw'
  have hout : ∀ k, k + 8 ≤ 32 → Outside (RunIface.gA + k) 8 (R.rt ++ win s 4800 40) := fun k hk => by
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [hMF.accessible]; exact hacc, hrt, ?_, by rw [hMF.accessible]; exact hwa, hwr, ?_⟩
  · rw [e1, hMF.readLE _ _ (hout 8 (by omega)), ← e1]; exact h1
  · rw [e2, hMF.readLE _ _ (hout 16 (by omega)), ← e2]; exact h2
  · rw [e3, hMF.readLE _ _ (hout 24 (by omega)), ← e3]; exact h3
  · rw [hMF.readLE _ _ (by simpa using hout 0 (by omega))]; exact h4
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hww ⊢; rw [hT]; omega

/-- The operand `*Int`s at a compute call: `IntPre` for the operands `xs` (each one of `base`, `exp`, `mod`). -/
theorem intPre_ops {R : RtInv} {b1 B : Nat} {L L1 : List (Nat × Nat)} {p len : BitVec 64} {s T : State}
    {M : Janus.Arm64.Memory} {W stkM aboveM : Nat} (xs : List Nat)
    (hT : (T.regs 4).toNat = (s.regs 4).toNat - 616) (hTm : T.mem = M) (hT14 : T.regs 14 = s.regs 14)
    (hTfs : T.fsBase = s.fsBase)
    (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (ha8 : 8 ≤ aboveM)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 14).toNat + 16) 8 L)
    (hfL : ApartAll (s.fsBase.toNat - 8) 8 L)
    (hsv : RunIface.Serves R) (hB : B ≤ b1)
    (hdS : Extracted.program.DataLoaded M) (hext : LiveExt R L L1)
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M))
    (hMF : MemFrame s.mem M (R.rt ++ win s 4800 40))
    (hop : ∀ j, j < 3 → OpDone R M s p len L L1 j) (hopA : OpsApart M s 3)
    (hxs : ∀ a ∈ xs, ∃ j, j < 3 ∧ a = opAt s j)
    (hpw : xs.Pairwise fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j) :
    RunIface.IntPre R b1 B L1 stkM aboveM xs T := by
  have hce := callEnv_c hT hTm hT14 hTfs henvW hW hW1 hab ha8 hdS hext hMF
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨⟨hfb, hfr, hfg⟩, hfrt, hfw⟩⟩ := henvW
  simp only [regSP, Janus.Amd64.GoABI.regG] at hb' ha hw hout hal hga hgr
  have hgl := globals_c hT hW hW1 hab hb' hglob hMF
  have hLs1 := liveSep_W hext hLs hout hb'
  unfold Apart at hga hfw
  have hint : ∀ j, j < 3 → RunIface.IntOK M R L1 (opAt s j) ∧
      (0 < M.readLE (opAt s j + 24) 8 →
        Outside (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (win s W 40) ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) ((s.regs 14).toNat + 16) 8 ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (s.fsBase.toNat - 8) 8) := by
    intro j hj
    obtain ⟨hneg, -, hnorm, -, hlc, hlive⟩ := hop j hj
    have hfa : ∀ (hc : 0 < M.readLE (opAt s j + 24) 8),
        Outside (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (win s W 40) ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) ((s.regs 14).toNat + 16) 8 ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (s.fsBase.toNat - 8) 8 := fun hc =>
      ⟨outside_of_inRanges (hlive hc).1 hLs1, apart_guard hext hgL hgr (hlive hc).1,
        apart_guard hext hfL hfrt (hlive hc).1⟩
    refine ⟨⟨hneg, by simp only [opAt]; omega, by simp only [opAt]; omega,
      by rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only [opAt]; omega) (by simp only [opAt]; omega),
      Or.inr (hout.of_sub (by simp only [opAt]; omega) (by simp only [opAt]; omega)),
      fun hc => ⟨(hlive hc).2.1, Or.inl (hlive hc).1, by rw [hMF.accessible]; exact (hlive hc).2.2.1, (hlive hc).2.2.2.1⟩,
      hlc, hnorm, fun hc => ?_⟩, hfa⟩
    have := (hfa hc).1
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this
    generalize M.readLE (opAt s j + 8) 8 = P at this ⊢
    generalize M.readLE (opAt s j + 24) 8 = C at this ⊢
    unfold Apart; simp only [opAt]; omega
  unfold RunIface.IntPre
  rw [hTm, hT14, hTfs]
  refine ⟨hce, hsv, hgl, hB, hinv, fun a ha => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hxs a ha
    obtain ⟨hI, hf⟩ := hint j hj
    refine ⟨hI, ?_, fun hc => ?_, by unfold Apart; simp only [opAt]; omega, fun hc => (hf hc).2.1,
      by unfold Apart; simp only [opAt]; omega, fun hc => (hf hc).2.2⟩
    · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; simp only [opAt]; omega
    · have := (hf hc).1
      simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; rw [hT]; omega
  · refine hpw.imp fun {a a'} ⟨i, j, hij, hj, ha, ha'⟩ => ?_
    subst ha ha'
    have hfi := (hint i (by omega)).2
    have hfj := (hint j hj).2
    refine ⟨by unfold Apart; simp only [opAt]; omega, fun hc => ?_, fun hc => ?_, fun hc hc' => hopA i j hij hj hc hc'⟩
    · have := (hfj hc).1
      simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this
      unfold Apart; simp only [opAt] at this ⊢; omega
    · have := (hfi hc).1
      simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this
      unfold Apart; simp only [opAt] at this ⊢; omega

/-- The memory after `Run`'s `CALL` pushed the return address at `e - 616`: the operand facts and frames carry over. -/
theorem push_facts {R : RtInv} {b : Nat} {L L1 : List (Nat × Nat)} {c p len cp : BitVec 64} {s S : State}
    {ret k ks cst b1 : Nat} (hrel : RelD R b L c p len cp s ret k ks cst L1 b1 S) (v : Nat) (hk : k ≤ 3)
    (hb' : 4800 ≤ (s.regs 4).toNat) (hout : Outside ((s.regs 4).toNat - 4800) (4800 + 40) R.rt)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true) (hro : RoOut R) :
    MemFrame s.mem (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) (R.rt ++ win s 4800 40) ∧
    LiveFrame S.mem (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) L1 [] ∧
    Extracted.program.DataLoaded (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) ∧
    R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v)) ∧
    (∀ j, j < k → OpDone R (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) s p len L L1 j) ∧
    OpsApart (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) s k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hdS, -, -, -, -, hinv, hLsS, hMF, -, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  have ho : Outside ((s.regs 4).toNat - 616) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hMF1 : MemFrame S.mem (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) (R.rt ++ win s 4800 40) := by
    simp only [win]; janus_frame
  have hLF1 : LiveFrame S.mem (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v) L1 [] :=
    LiveFrame.of_win (by simp only [win]; janus_frame) hLsS
  have hrd : ∀ j, j ≤ 2 → ∀ o, o + 8 ≤ 32 →
      (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v).readLE (opAt s j + o) 8 = S.mem.readLE (opAt s j + o) 8 := by
    intro j hj o ho
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp only [opAt]; omega)
  refine ⟨hMF.trans hMF1 fun _ _ h => ⟨h, h⟩, hLF1, ?_, by rw [view_writeLE_out ho]; exact hinv, fun j hj => ?_, ?_⟩
  · exact dataLoaded_frame64 hdS (by simp) hro hMF1 (fun r hr _ => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega))
  · have hj3 : j ≤ 2 := by omega
    exact (hop j hj).transport
      (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp only [opAt]; omega))
      (by simpa using hrd j hj3 8 (by omega)) (by simpa using hrd j hj3 16 (by omega))
      (by simpa using hrd j hj3 24 (by omega)) hLF1 (fun _ _ h => h)
  · exact hopA.transport fun i hi => ⟨by simpa using hrd i (by omega) 8 (by omega),
      by simpa using hrd i (by omega) 24 (by omega)⟩

end FvModexp.Amd64.Run
