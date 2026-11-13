import FvModexp.Proofs.Arm64.Exp.ModInvRt

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `zz := nat(nil).make(2·numWords)` (nat.go:1322, nat.go:68) (agent infra)

Small-context lemma at `+0x1e0` (`0x1b6dd0`): `makeslice(Word, 2·numWords, 2·numWords + 4)` and the reloads, up to
`+0x234` (`0x1b6e24`, the `setWord` test).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

/-- the facts after `zz := nat(nil).make(2 · numWords)` (raw) -/
@[reducible] def AllocPostZ (R : RtInv) (L : List (Nat × Nat)) (b g sp nw : Nat) (M m : Memory) (p r : Nat) : Prop :=
  MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 96, sp + 104), (sp + 136, sp + 144)]) ∧
  LiveFrame M m L [] ∧ m.regions = M.regions ∧ InRanges p r R.rt ∧ ApartAll p r L ∧ p + r ≤ 2 ^ 48 ∧
  m.accessible p (8 * (2 * nw + 4)) true = true ∧ p % 8 = 0 ∧ 8 * (2 * nw + 4) ≤ r ∧ b - blockSize (8 * (2 * nw + 4)) true ≤ b - r ∧
  R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zzalloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ra : BitVec 64) (Q : State → Prop) (b : Nat) (L : List (Nat × Nat)) (g sp kc nw : Nat) (M : Memory)
    (r18 r29 : BitVec 64) (he : Env R L g sp kc M) (hkc : 4608 ≤ kc) (hnw : 0 < nw) (hnw2 : nw ≤ 2 ^ 12)
    (ht8 : M.readLE wT 8 = 8) (ht0 : M.readLE (wT + 8) 8 = 0) (hta : M.accessible wT 16 false = true)
    (hwt : Apart wT 16 (sp - kc) (kc + 312)) (hty : Outside wT 16 R.rt)
    (hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * nw, 2 * nw + 4])
    (hbs : blockSize (8 * (2 * nw + 4)) true ≤ b) (hinv : R.inv b L g (view R.rt L M))
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Nat)
    (r0 : M.readLE (sp + 208) 8 = v0) (r1 : M.readLE (sp + 88) 8 = v1) (r2 : M.readLE (sp + 192) 8 = v2)
    (r3 : M.readLE (sp + 272) 8 = v3) (r4 : M.readLE (sp + 280) 8 = v4) (r5 : M.readLE (sp + 288) 8 = v5)
    (r6 : M.readLE (sp + 296) 8 = v6) (r7 : M.readLE (sp + 304) 8 = v7) (r8 : M.readLE (sp + 200) 8 = v8)
    (r9 : M.readLE (sp + 128) 8 = v9) (r10 : M.readLE (sp + 152) 8 = v10)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1797584) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h11 : S.regs 11 = BitVec.ofNat 64 (2 * nw))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KZ : ∀ (S' : State) (m : Memory) (p r : Nat),
      S'.pc = BitVec.ofNat 64 1797668 → S'.sp = BitVec.ofNat 64 sp → S'.regs 13 = BitVec.ofNat 64 p →
      S'.regs 12 = BitVec.ofNat 64 (2 * nw) → S'.regs 11 = BitVec.ofNat 64 (2 * nw + 4) →
      S'.regs 0 = BitVec.ofNat 64 v0 → S'.regs 1 = BitVec.ofNat 64 v1 → S'.regs 2 = BitVec.ofNat 64 v2 →
      S'.regs 3 = BitVec.ofNat 64 v3 → S'.regs 4 = BitVec.ofNat 64 v4 → S'.regs 5 = BitVec.ofNat 64 v5 →
      S'.regs 6 = BitVec.ofNat 64 v6 → S'.regs 7 = BitVec.ofNat 64 v7 → S'.regs 8 = BitVec.ofNat 64 v8 →
      S'.regs 9 = BitVec.ofNat 64 v9 → S'.regs 10 = BitVec.ofNat 64 v10 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = m →
      AllocPostZ R L b g sp nw M m p r → ReachesRet (LibW.program.link impl) ra S' Q) :
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
  have t8 : ((M.writeLE (sp + 136) 8 (2 * nw)).writeLE (sp + 96) 8 (2 * nw + 4)).readLE 2641088 8 = 8 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact ht8
  have t0 : ((M.writeLE (sp + 136) 8 (2 * nw)).writeLE (sp + 96) 8 (2 * nw + 4)).readLE (2641088 + 8) 8 = 0 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact ht0
  janus_run [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, t8, t0] until [1797668] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv' _ _
  refine KZ _ m ptr.toNat (blockSize (8 * (2 * nw + 4)) true) ?_ ?_ (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; janus_simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    ⟨?_, ?_, hrg1, hIn, hAp, hle, ?_, h8 (Or.inr (by omega)), hsz, Nat.le_refl _, hinv'⟩
  all_goals first | (janus_simp; done) | skip
  · have hw1 : MemFrame M ((M.writeLE (sp + 136) 8 (2 * nw)).writeLE (sp + 96) 8 (2 * nw + 4))
        [(sp + 96, sp + 104), (sp + 136, sp + 144)] :=
      ((MemFrame.refl M _).writeLE_inRanges _ ⟨(sp + 136, sp + 144), by simp, by simp only; omega,
        by simp only; omega⟩).writeLE_inRanges _ ⟨(sp + 96, sp + 104), by simp, by simp only; omega,
        by simp only; omega⟩
    refine hw1.trans hMF (fun a k ho => ⟨?_, ?_⟩)
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
  · have hLw : LiveFrame M ((M.writeLE (sp + 136) 8 (2 * nw)).writeLE (sp + 96) 8 (2 * nw + 4)) L [] :=
      ((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
    exact hLw.trans hLF (fun _ _ h => h)
  · rw [hMF.accessible]; simp only [Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z.setWord(k0)` (nat.go:72-80, result discarded) for `k0 ≠ 0`, `cap z > 0`: `z[0] = k0`, then `i = 2` and the jump
to the loop head (`+0x234 → +0x3c0`) -/
theorem setw (impl : List Segment) (ra : BitVec 64) (Q : State → Prop) (p c k sp : Nat) (M : Memory)
    (hk0 : 0 < k) (hk : k < 2 ^ 64) (hc : 0 < c) (hc64 : c < 2 ^ 64) (hp : p < 2 ^ 64)
    (hacc : M.accessible p 8 true = true)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1797668) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h10 : S.regs 10 = BitVec.ofNat 64 k)
    (hmem : S.mem = M)
    (KS : ∀ S' : State, S'.pc = BitVec.ofNat 64 1798064 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 2 → S'.regs 14 = BitVec.ofNat 64 p →
      (∀ i, i ≠ 0 → i ≠ 14 → i < 31 → S'.regs i = S.regs i) → S'.mem = M.writeLE p 8 k →
      ReachesRet (LibW.program.link impl) ra S' Q) :
    ReachesRet (LibW.program.link impl) ra S Q := by
  have hk' : BitVec.ofNat 64 k ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hc' : BitVec.ofNat 64 c ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [hk', hc'] until [1798064]
  refine KS _ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  intro i hi0 hi14 _
  simp only [setReg, if_neg hi0, if_neg hi14]

end FvModexp.Arm64.ModInv
