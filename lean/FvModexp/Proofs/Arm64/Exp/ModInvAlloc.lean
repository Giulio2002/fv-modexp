import FvModexp.Proofs.Arm64.Exp.ModInvSeg2

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the allocating `z.make(numWords + 1)` (nat.go:68) (agent infra)

A small-context lemma over an abstract state at `+0xd8` (`0x1b6cc8`, the `BLT` target of `cap z < numWords + 1`):
`makeslice(Word, numWords + 1, numWords + 5)`, the reloads, up to `JM` (`+0x15c`). The frame is described by the
in-frame stack pointer `sp = SP_entry - 240` (window `[sp - kc, sp + 312)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

/-- the frame environment at memory `M` (in-frame `SP = sp`, callee stack bound `kc`) -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (g sp kc : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ kc ≤ sp ∧ sp + 312 ≤ 2 ^ 48 ∧ M.accessible (sp - kc) (kc + 312) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + kc < sp ∧
  Outside (sp - kc) (kc + 312) R.rt ∧ Apart (g + 16) 8 (sp - kc) (kc + 312) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - kc, sp + 312)]

/-- `type:big.Word` -/
abbrev wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- the `Word` type descriptor's size / pointer words (as divmc's `StackNat.wT_facts`) -/
theorem wT_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE wT 8 = 8 ∧ m.readLE (wT + 8) 8 = 0 ∧ m.accessible wT 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

/-- the facts after the allocating `make` (raw: the caller turns them into `JM`'s) -/
@[reducible] def AllocPost (R : RtInv) (L : List (Nat × Nat)) (b g sp nw : Nat) (M m : Memory) (p r : Nat) : Prop :=
  MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 104, sp + 112), (sp + 144, sp + 152)]) ∧
  LiveFrame M m L [] ∧ m.regions = M.regions ∧ InRanges p r R.rt ∧ ApartAll p r L ∧ p + r ≤ 2 ^ 48 ∧
  m.accessible p (8 * (nw + 5)) true = true ∧ p % 8 = 0 ∧ 8 * (nw + 5) ≤ r ∧ b - blockSize (8 * (nw + 5)) true ≤ b - r ∧
  R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zalloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ra : BitVec 64) (Q : State → Prop) (b : Nat) (L : List (Nat × Nat)) (g sp kc nw : Nat) (M : Memory)
    (r18 r29 : BitVec 64) (he : Env R L g sp kc M) (hkc : 4608 ≤ kc) (hnw : 0 < nw) (hnw2 : nw ≤ 2 ^ 12)
    (ht8 : M.readLE wT 8 = 8) (ht0 : M.readLE (wT + 8) 8 = 0) (hta : M.accessible wT 16 false = true)
    (hwt : Apart wT 16 (sp - kc) (kc + 312)) (hty : Outside wT 16 R.rt)
    (hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, nw + 1, nw + 5])
    (hbs : blockSize (8 * (nw + 5)) true ≤ b) (hinv : R.inv b L g (view R.rt L M))
    (v3 v4 v5 v6 v7 v8 v9 v10 : Nat)
    (r3 : M.readLE (sp + 272) 8 = v3) (r4 : M.readLE (sp + 280) 8 = v4) (r5 : M.readLE (sp + 288) 8 = v5)
    (r6 : M.readLE (sp + 296) 8 = v6) (r7 : M.readLE (sp + 304) 8 = v7) (r8 : M.readLE (sp + 200) 8 = v8)
    (r9 : M.readLE (sp + 128) 8 = v9) (r10 : M.readLE (sp + 152) 8 = v10)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1797320) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h1 : S.regs 1 = BitVec.ofNat 64 (nw + 1)) (h9 : S.regs 9 = BitVec.ofNat 64 nw)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KZ : ∀ (S' : State) (m : Memory) (p r : Nat),
      S'.pc = BitVec.ofNat 64 1797452 → S'.sp = BitVec.ofNat 64 sp → S'.regs 0 = BitVec.ofNat 64 p →
      S'.regs 1 = BitVec.ofNat 64 (nw + 1) → S'.regs 2 = BitVec.ofNat 64 (nw + 5) →
      S'.regs 3 = BitVec.ofNat 64 v3 → S'.regs 4 = BitVec.ofNat 64 v4 → S'.regs 5 = BitVec.ofNat 64 v5 →
      S'.regs 6 = BitVec.ofNat 64 v6 → S'.regs 7 = BitVec.ofNat 64 v7 → S'.regs 8 = BitVec.ofNat 64 v8 →
      S'.regs 9 = BitVec.ofNat 64 v9 → S'.regs 10 = BitVec.ofNat 64 v10 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = m →
      AllocPost R L b g sp nw M m p r → ReachesRet (LibW.program.link impl) ra S' Q) :
    ReachesRet (LibW.program.link impl) ra S Q := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have hwTv : wT = 2641088 := rfl
  rw [hwTv] at ht8 ht0 hta hwt hty hok
  unfold Apart at hwt hgw
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have t8 : ((M.writeLE (sp + 144) 8 (nw + 1)).writeLE (sp + 104) 8 (nw + 5)).readLE 2641088 8 = 8 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact ht8
  have t0 : ((M.writeLE (sp + 144) 8 (nw + 1)).writeLE (sp + 104) 8 (nw + 5)).readLE (2641088 + 8) 8 = 0 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact ht0
  janus_run [r3, r4, r5, r6, r7, r8, r9, r10, t8, t0] until [1797452] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv' _ _
  refine KZ _ m ptr.toNat (blockSize (8 * (nw + 5)) true) ?_ ?_ (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; janus_simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    ⟨?_, ?_, hrg1, hIn, hAp, hle, ?_, h8 (Or.inr (by omega)), hsz, Nat.le_refl _, hinv'⟩
  all_goals first | (janus_simp; done) | skip
  · have hw1 : MemFrame M ((M.writeLE (sp + 144) 8 (nw + 1)).writeLE (sp + 104) 8 (nw + 5))
        [(sp + 104, sp + 112), (sp + 144, sp + 152)] :=
      ((MemFrame.refl M _).writeLE_inRanges _ ⟨(sp + 144, sp + 152), by simp, by simp only; omega,
        by simp only; omega⟩).writeLE_inRanges _ ⟨(sp + 104, sp + 112), by simp, by simp only; omega,
        by simp only; omega⟩
    refine hw1.trans hMF (fun a k ho => ⟨?_, ?_⟩)
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
  · have hLw : LiveFrame M ((M.writeLE (sp + 144) 8 (nw + 1)).writeLE (sp + 104) 8 (nw + 5)) L [] :=
      ((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
    exact hLw.trans hLF (fun _ _ h => h)
  · rw [hMF.accessible]; simp only [Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)

end FvModexp.Arm64.ModInv
