import FvModexp.Proofs.Arm64.Top.RunCDefs

/-!
# `Run` (arm64): the compute calls — the callee preconditions from `Run`'s state

`Run` calls `(*Int).Mod` / `(*Int).exp` on its stack `big.Int`s (`base` at `SP - 136`, `exp` at `SP - 168`, `mod` at
`SP - 200`, `SP` = `Run`'s entry `SP`; the callee's `SP` is `SP - 624`), then `(*Int).Bytes` on the result. The lemmas here
build `RunIface.IntPre` for these calls from `Run`'s precondition (`CallEnv` with a window `W ≥ 624 + stkM`, `Globals`,
the `stackguard0` word apart from the caller's objects) and the operand facts (`OpDone`, `OpsApart`), in small contexts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem outside_of_inRanges {a n : Nat} {L ws : List (Nat × Nat)} (h : InRanges a n L) (hs : LiveSep L ws) :
    Outside a n ws := by
  obtain ⟨r, hr, h1, h2⟩ := h
  exact (hs r hr).of_sub h1 (by omega)

/-- An object of the extended live set is apart from the `stackguard0` word: old objects by the caller's premise, new
ones because they are runtime-owned and the word is not. -/
theorem apart_guard {R : RtInv} {L L1 : List (Nat × Nat)} {g a n : Nat} (hext : LiveExt R L L1)
    (hgL : ApartAll g 8 L) (hgr : Outside g 8 R.rt) (h : InRanges a n L1) : Apart a n g 8 := by
  obtain ⟨ns, rfl, hns, -⟩ := hext
  obtain ⟨r, hr, h1, h2⟩ := h
  rcases List.mem_append.1 hr with hr | hr
  · have := hgL r hr; unfold Apart at this ⊢; omega
  · have := InRanges.apart (hns r hr).1 hgr; unfold Apart at this ⊢; omega

/-- `IntPre` reads only `SP`, the memory and `X28` of the state. -/
theorem intPre_congr {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {xs : List Nat} {s t : State}
    (h : RunIface.IntPre R b B L stk above xs s) (hsp : t.sp = s.sp) (hm : t.mem = s.mem) (h28 : t.regs 28 = s.regs 28) :
    RunIface.IntPre R b B L stk above xs t := by
  unfold RunIface.IntPre CallEnv GuardOK StackOK win at *
  rw [hsp, hm, h28]; exact h

/-- The live set of the operand phase is outside `Run`'s whole window `W`. -/
theorem liveSep_W {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {W : Nat} (hext : LiveExt R L L1)
    (hLs : LiveSep L (win s W 40)) (hout : Outside (s.sp.toNat - W) (W + 40) R.rt) (hW : W ≤ s.sp.toNat) :
    LiveSep L1 (win s W 40) :=
  hext.liveSep hLs fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by dsimp only; omega)

/-- The callee's `CallEnv` at `Run`'s call sites (`SP - 624`), from `Run`'s with window `W ≥ 624 + stkM`. -/
theorem callEnv_c {R : RtInv} {L L1 : List (Nat × Nat)} {s T : State} {M : Memory} {W stkM aboveM : Nat}
    (hT : T.sp.toNat = s.sp.toNat - 624) (hTm : T.mem = M) (hT28 : T.regs 28 = s.regs 28)
    (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hdS : Extracted.program.DataLoaded M) (hext : LiveExt R L L1)
    (hMF : MemFrame s.mem M (R.rt ++ winA s 4800 40)) :
    CallEnv R L1 T stkM aboveM := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  have hLs1 := liveSep_W hext hLs hout hb'
  unfold Apart at hga
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, by omega, by omega⟩)
  unfold CallEnv GuardOK StackOK
  rw [hT, hTm, hT28]
  refine ⟨⟨hg1, by rw [hMF.accessible]; exact hg2, by rw [hgM]; omega⟩,
    ⟨by omega, by omega, by omega, by rw [hMF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩,
    hdS, hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, ?_, hro⟩
  intro r hr
  have := hLs1 r hr
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
  omega

/-- `Globals` at the callee's state, from `Run`'s. -/
theorem globals_c {R : RtInv} {s T : State} {M : Memory} {W stkM aboveM : Nat}
    (hT : T.sp.toNat = s.sp.toNat - 624) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hsW : W ≤ s.sp.toNat)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hMF : MemFrame s.mem M (R.rt ++ winA s 4800 40)) :
    RunIface.Globals R M (win T stkM aboveM) := by
  obtain ⟨h1, h2, h3, h4, e1, e2, e3, hacc, hrt, hw, hwa, hwr, hww⟩ := hglob
  have hw' := hw
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hw'
  have hout : ∀ k, k + 8 ≤ 32 → Outside (RunIface.gA + k) 8 (R.rt ++ winA s 4800 40) := fun k hk => by
    simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [hMF.accessible]; exact hacc, hrt, ?_, by rw [hMF.accessible]; exact hwa, hwr, ?_⟩
  · rw [e1, hMF.readLE _ _ (hout 8 (by omega)), ← e1]; exact h1
  · rw [e2, hMF.readLE _ _ (hout 16 (by omega)), ← e2]; exact h2
  · rw [e3, hMF.readLE _ _ (hout 24 (by omega)), ← e3]; exact h3
  · rw [hMF.readLE _ _ (by simpa using hout 0 (by omega))]; exact h4
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hww ⊢; rw [hT]; omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The operand `*Int`s at a compute call: `IntPre` for the operands `xs` (each one of `base`, `exp`, `mod`, in slot
order). -/
theorem intPre_ops {R : RtInv} {b1 B : Nat} {L L1 : List (Nat × Nat)} {p len : BitVec 64} {s T : State} {M : Memory}
    {W stkM aboveM : Nat} (xs : List Nat)
    (hT : T.sp.toNat = s.sp.toNat - 624) (hTm : T.mem = M) (hT28 : T.regs 28 = s.regs 28)
    (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hsv : RunIface.Serves R) (hB : B ≤ b1)
    (hdS : Extracted.program.DataLoaded M) (hext : LiveExt R L L1)
    (hinv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M))
    (hMF : MemFrame s.mem M (R.rt ++ winA s 4800 40))
    (hop : ∀ j, j < 3 → OpDone R M s p len L L1 j) (hopA : OpsApart M s 3)
    (hxs : ∀ a ∈ xs, ∃ j, j < 3 ∧ a = opAt s j)
    (hpw : xs.Pairwise fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j) :
    RunIface.IntPre R b1 B L1 stkM aboveM xs T := by
  have hce := callEnv_c hT hTm hT28 henvW hW hW1 hab hdS hext hMF
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  have hgl := globals_c hT hW hW1 hab hb' hglob hMF
  have hLs1 := liveSep_W hext hLs hout hb'
  unfold Apart at hga
  -- per operand
  have hint : ∀ j, j < 3 → RunIface.IntOK M R L1 (opAt s j) ∧
      (0 < M.readLE (opAt s j + 24) 8 →
        Outside (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (win s W 40) ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) ((s.regs 28).toNat + 16) 8) := by
    intro j hj
    obtain ⟨hneg, -, hnorm, -, hlc, hlive⟩ := hop j hj
    have hfa : ∀ (hc : 0 < M.readLE (opAt s j + 24) 8),
        Outside (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) (win s W 40) ∧
        Apart (M.readLE (opAt s j + 8) 8) (8 * M.readLE (opAt s j + 24) 8) ((s.regs 28).toNat + 16) 8 := fun hc =>
      ⟨outside_of_inRanges (hlive hc).1 hLs1, apart_guard hext hgL hgr (hlive hc).1⟩
    refine ⟨⟨hneg, by simp only [opAt]; omega, by simp only [opAt]; omega,
      by rw [hMF.accessible]; exact Memory.accessible_mono _ hw (by simp only [opAt]; omega) (by simp only [opAt]; omega),
      Or.inr (hout.of_sub (by simp only [opAt]; omega) (by simp only [opAt]; omega)),
      fun hc => ⟨(hlive hc).2.1, Or.inl (hlive hc).1, by rw [hMF.accessible]; exact (hlive hc).2.2.1, (hlive hc).2.2.2.1⟩,
      hlc, hnorm, fun hc => ?_⟩, hfa⟩
    have := (hfa hc).1
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this
    generalize M.readLE (opAt s j + 8) 8 = P at this ⊢
    generalize M.readLE (opAt s j + 24) 8 = C at this ⊢
    unfold Apart; simp only [opAt]; omega
  unfold RunIface.IntPre
  rw [hTm, hT28]
  refine ⟨hce, hsv, hgl, hB, hinv, fun a ha => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hxs a ha
    obtain ⟨hI, hf⟩ := hint j hj
    refine ⟨hI, ?_, fun hc => ?_, by unfold Apart; simp only [opAt]; omega, fun hc => (hf hc).2⟩
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

end FvModexp.Arm64.Run
