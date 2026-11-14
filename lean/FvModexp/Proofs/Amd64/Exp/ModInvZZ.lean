import FvModexp.Proofs.Amd64.Exp.ModInvSeg3

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `zz := nat(nil).make(2·numWords)` (nat.go:1322) (agent infra s55; twin
of `Arm64/Exp/ModInvZZ`)

From `JM` (`+0x1b6`): the spills `0xc0(SP') = z.ptr` (`RSP - 32`), `0x50(SP') = numWords + 1` (`RSP - 144`),
`0xb8(SP') = cap z` (`RSP - 40`), `2·numWords > 1` (the `makeslice` path at `+0x262`), the spills
`0x80(SP') = 2·numWords` (`RSP - 96`), `0x58(SP') = 2·numWords + 4` (`RSP - 136`), `makeslice(Word, 2·numWords,
2·numWords + 4)` (CALL at `+0x281`), the reloads, up to `+0x2e0` (`z.setWord(k0)`). `zzalloc` hands the raw facts
(`AllocPostZ`) to a continuation.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- the facts after `zz := nat(nil).make(2·numWords)` (`M` = memory at `JM`, `sp` = the entry `RSP`) -/
@[reducible] def AllocPostZ (R : RtInv) (L : List (Nat × Nat)) (b g sp nw : Nat) (M m : Memory) (p r : Nat) : Prop :=
  MemFrame M m (R.rt ++ [(sp - 232 - 4096, sp - 200), (sp - 144, sp - 128), (sp - 96, sp - 88), (sp - 40, sp - 24)]) ∧
  LiveFrame M m L [] ∧ m.regions = M.regions ∧ InRanges p r R.rt ∧ ApartAll p r L ∧ p + r ≤ 2 ^ 48 ∧
  m.accessible p (8 * (2 * nw + 4)) true = true ∧ p % 8 = 0 ∧ 8 * (2 * nw + 4) ≤ r ∧ r ≤ makeCost (2 * nw) ∧
  R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem zzalloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (s : State) (nw zp' zc' : Nat) (hkc : 4096 ≤ kc)
    (hsp : 232 + kc ≤ (s.regs 4).toNat) (hsp2 : (s.regs 4).toNat + 72 ≤ 2 ^ 48) (hal : (s.regs 4).toNat % 8 = 0)
    (hnw : 2 ≤ nw) (hnw2 : nw ≤ 2 ^ 12) (hzp : zp' < 2 ^ 64) (hzc : zc' < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x1b6))
    (h4 : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224)) (h5 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (hab : Abi s S) (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zc')
    (h2 : S.regs 2 = BitVec.ofNat 64 (nw + 1)) (h3 : S.regs 3 = BitVec.ofNat 64 nw)
    (hw : S.mem.accessible ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) true = true)
    (hout : Outside ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) R.rt)
    (hLs : LiveSep L [((s.regs 4).toNat - (232 + kc), (s.regs 4).toNat + 72)])
    (ht8 : S.mem.readLE 7233184 8 = 8) (ht0 : S.mem.readLE 7233192 8 = 0)
    (hwt : Apart 7233184 16 ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72)) (hty : Outside 7233184 16 R.rt)
    (hok : R.ok (cA "runtime.makeslice") [7233184, 2 * nw, 2 * nw + 4])
    (hta : S.mem.accessible 7233184 16 false = true) (hgw : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hga : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgA : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72))
    (hgr : S.mem.readLE ((s.regs 14).toNat + 16) 8 + (232 + kc) < (s.regs 4).toNat)
    (hbs : makeCost (2 * nw) ≤ b) (hinv : R.inv b L (s.regs 14).toNat (view R.rt L S.mem))
    (Q : State → Prop)
    (KZ : ∀ (S' : State) (m : Memory) (p r : Nat),
      S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x2e0) → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → Abi s S' →
      S'.regs 15 = BitVec.ofNat 64 p → S'.regs 13 = BitVec.ofNat 64 (2 * nw) →
      S'.regs 11 = BitVec.ofNat 64 (2 * nw + 4) → S'.regs 0 = BitVec.ofNat 64 zp' →
      S'.regs 1 = BitVec.ofNat 64 zc' → S'.regs 2 = BitVec.ofNat 64 (nw + 1) →
      S'.regs 3 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 120) 8) →
      S'.regs 6 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 264) 8) →
      S'.regs 7 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 256) 8) →
      S'.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 272) 8) →
      S'.regs 9 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 280) 8) →
      S'.regs 10 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 288) 8) →
      S'.regs 12 = BitVec.ofNat 64 (S.mem.readLE ((s.regs 4).toNat - 224 + 144) 8) →
      m.readLE ((s.regs 4).toNat - 224 + 192) 8 = zp' → S'.mem = m →
      AllocPostZ R L b (s.regs 14).toNat (s.regs 4).toNat nw S.mem m p r →
      ReachesRet (LibW.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨a14, afs, ax15, adf⟩ := hab
  have hmc : makeCost (2 * nw) = allocCost (8 * (2 * nw + 4)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (2 * nw = 1) by omega)]
  have hbl := blockSize_le_allocCost (8 * (2 * nw + 4)) true
  have hbs' : blockSize (8 * (2 * nw + 4)) true ≤ b := by omega
  unfold Apart at hwt hgA
  have tg : ((((((S.mem.writeLE ((s.regs 4).toNat - 224 + 192) 8 zp').writeLE ((s.regs 4).toNat - 224 + 80) 8 (nw + 1)).writeLE
      ((s.regs 4).toNat - 224 + 184) 8 zc').writeLE ((s.regs 4).toNat - 224 + 128) 8 (2 * nw)).writeLE
      ((s.regs 4).toNat - 224 + 88) 8 (2 * nw + 4)).writeLE ((s.regs 4).toNat - 224 - 8) 8 6204230).readLE
      ((s.regs 14).toNat + 16) 8 = S.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hLs0 := hLs
  simp only [LiveSep] at hLs
  have m1 : nw % 18446744073709551616 = nw := Nat.mod_eq_of_lt (by omega)
  have m2 : (2 * nw) % 18446744073709551616 = 2 * nw := Nat.mod_eq_of_lt (by omega)
  have m3 : (2 * nw + 4) % 18446744073709551616 = 2 * nw + 4 := Nat.mod_eq_of_lt (by omega)
  have m4 : 2 * nw + 4 < 9223372036854775808 := by omega
  have m5 : 8 * (2 * nw + 4) ≤ 281474976710656 := by omega
  have m6 : (nw + 1) % 18446744073709551616 = nw + 1 := Nat.mod_eq_of_lt (by omega)
  have hadd : BitVec.ofNat 64 nw + BitVec.ofNat 64 nw = BitVec.ofNat 64 (2 * nw) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus64_run [BitVec.msb_eq_decide, ht8, ht0, tg, m1, m2, m3, m6, hadd] until [0x5ea8c0 + 0x2e0] calls [hmk.pos L b]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv'
  have hsz : 8 * (2 * nw + 4) ≤ blockSize (8 * (2 * nw + 4)) true := Janus.Contracts.AllocSat.le_blockSize _ _
  refine KZ _ m ptr.toNat (blockSize (8 * (2 * nw + 4)) true) ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl ⟨?mf, ?lf, hrg1, hIn, hAp, hle, ?acc, h8 (Or.inr (by omega)), hsz, by omega, hinv'⟩
  case mf =>
    have hw1 : MemFrame S.mem ((((((S.mem.writeLE ((s.regs 4).toNat - 224 + 192) 8 zp').writeLE ((s.regs 4).toNat - 224 + 80) 8 (nw + 1)).writeLE
          ((s.regs 4).toNat - 224 + 184) 8 zc').writeLE ((s.regs 4).toNat - 224 + 128) 8 (2 * nw)).writeLE
          ((s.regs 4).toNat - 224 + 88) 8 (2 * nw + 4)).writeLE ((s.regs 4).toNat - 224 - 8) 8 6204230)
        [((s.regs 4).toNat - 232 - 4096, (s.regs 4).toNat - 200), ((s.regs 4).toNat - 144, (s.regs 4).toNat - 128),
          ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 24)] := by
      refine ((((((MemFrame.refl S.mem _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 40, (s.regs 4).toNat - 24), by simp,
        by simp only; omega, by simp only; omega⟩).writeLE_inRanges _ ⟨((s.regs 4).toNat - 144, (s.regs 4).toNat - 128),
        by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _ ⟨((s.regs 4).toNat - 40,
        (s.regs 4).toNat - 24), by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 96, (s.regs 4).toNat - 88), by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 144, (s.regs 4).toNat - 128), by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 232 - 4096, (s.regs 4).toNat - 200), by simp, by simp only; omega, by simp only; omega⟩
    refine hw1.trans hMF (fun a k ho => ⟨?_, ?_⟩)
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega, by omega⟩
  case lf =>
    have hLw : LiveFrame S.mem ((((((S.mem.writeLE ((s.regs 4).toNat - 224 + 192) 8 zp').writeLE ((s.regs 4).toNat - 224 + 80) 8 (nw + 1)).writeLE
          ((s.regs 4).toNat - 224 + 184) 8 zc').writeLE ((s.regs 4).toNat - 224 + 128) 8 (2 * nw)).writeLE
          ((s.regs 4).toNat - 224 + 88) 8 (2 * nw + 4)).writeLE ((s.regs 4).toNat - 224 - 8) 8 6204230) L [] :=
      ((((((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs0 (by omega) (by omega))
    exact hLw.trans hLF (fun _ _ h => h)
  case acc =>
    rw [hMF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  all_goals janus64_simp
  all_goals first | exact afs | exact a14 | exact ax15 | exact adf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z.setWord(k0)` (nat.go:72-80, result discarded) for `k0 ≠ 0`, `cap z > 0`: `z[0] = k0`, the reload of `z.ptr`,
then `i = 2` and the jump to the loop head (`+0x2e0 → +0x4ef`) -/
theorem setw (impl : List Amd64.Segment) (ra : BitVec 64) (Q : State → Prop) (p c k sp : Nat) (M : Memory)
    (hk0 : 0 < k) (hk : k < 2 ^ 64) (hc : 0 < c) (hc64 : c < 2 ^ 64) (hp : p < 2 ^ 64) (hsp : 224 ≤ sp) (hsp2 : sp ≤ 2 ^ 48)
    (hacc : M.accessible p 8 true = true) (hsa : M.accessible (sp - 224 + 192) 8 false = true) (hsl : M.readLE (sp - 224 + 192) 8 = p)
    (hap : p + 8 ≤ sp - 224 + 192 ∨ sp - 224 + 200 ≤ p)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x2e0)) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 c) (h12 : S.regs 12 = BitVec.ofNat 64 k)
    (hmem : S.mem = M)
    (KS : ∀ S' : State, S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x4ef) → S'.regs 12 = BitVec.ofNat 64 2 →
      S'.regs 0 = BitVec.ofNat 64 p → (∀ i, i ≠ 0 → i ≠ 12 → S'.regs i = S.regs i) →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M.writeLE p 8 k →
      ReachesRet (LibW.program.link impl) ra S' Q) :
    ReachesRet (LibW.program.link impl) ra S Q := by
  have hk' : BitVec.ofNat 64 k ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hc' : BitVec.ofNat 64 c ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hsl' : (M.writeLE p 8 k).readLE (sp - 224 + 192) 8 = p := by
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hsl
  janus64_run [hk', hc', hsl'] until [0x5ea8c0 + 0x4ef]
  refine KS _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | skip
  intro i hi0 hi12
  simp only [setRegF, if_neg hi0, if_neg hi12]

end FvModexp.Amd64.ModInv
