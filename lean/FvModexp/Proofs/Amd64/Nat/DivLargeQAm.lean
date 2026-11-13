import FvModexp.Proofs.Amd64.Nat.DivLargeQAl

set_option autoImplicit false

/-!
# `divLarge` (amd64): `q = z.make(m + 1)` allocating (`cap z < m + 1`), `m ≠ 0`: `makeslice(Word, m + 1, m + 5)`

From the alias test (`AtAl`): `alias(z, u)` false (or `cap z = 0`), `BX = m`, `R9 = m + 1`, `CMPQ R13 = cap z, R9; JL`
taken → `+0x4c0`: `TESTQ BX; JNE +0x524`: spill `R9` (`SP' + 0xa0`), `CX = m + 5` (`SP' + 0x70`), `makeslice` (`+0x540`),
reloads, `R15 = ptr`, `R13 = m + 5` → `joinQ`. Port of `Arm64/Nat/DivLargeQAm.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp.Amd64.DivBasic (LiveFrame.trans')

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem qAm (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDivL.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) (hz : zc < il - vl + 1)
    (hm0 : il - vl ≠ 0) (hb : makeCost (il - vl + 1) ≤ bk) (Q : State → Prop)
    (k : ∀ T Lq bq qp qc, AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hpre := hE.pre
  have hU := hS.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hz40 := hpre.zo.1
  have hMU := hS.mem
  have hM := hMU.mem
  have m1 := hM.s3; have m2 := hM.s1; have m3 := hM.mm
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hr6 := hS.r6; have hr8 := hS.r8
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  have hd : Extracted.program.DataLoaded s.mem := hpre.ce.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hSacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  have hsv := hpre.sv
  obtain ⟨hty, hwt, hWr⟩ := Mem.wordK hE hM
  have hk1' : il - vl + 1 ≠ 1 := by omega
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, il - vl + 1, il - vl + 5] := hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (il - vl + 1) = allocCost (8 * (il - vl + 1 + 4)) := by
    unfold makeCost makeCap; rw [if_neg hk1']
  have hbl := blockSize_le_allocCost (8 * (il - vl + 1 + 4)) true
  have hbs : blockSize (8 * (il - vl + 1 + 4)) true ≤ bk := by omega
  have hinv2 := hM.inv
  have hga := hpre.ce.2.2.2.2.2.1
  unfold Apart at hwt hga
  have hgS := hMU.grd
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
  obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S.mem.readLE 7233184 8 = 8 := (hWr _ _ (by omega) (by omega)).trans hws
  have hT2 : S.mem.readLE 7233192 8 = 0 := (hWr _ _ (by omega) (by omega)).trans hwp
  have hTa : S.mem.accessible 7233184 16 false = true := (hSacc _ _ _).trans hwa
  have hLs1 := lsep_of hE hS.ext2
  have hc1 := hE.c1len
  have hw1h : Held R Lk w1 (8 * c1) := hS.ext2.held (hE.w1live (by simp only [StackNat.rnd] at hc1; omega)).2.1
  have hm0' : (BitVec.ofNat 64 (il - vl) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  by_cases hz0 : zc = 0
  · subst hz0
    janus64_run [m1, m2, m3, hm0', hT1, hT2, hTa, hgS, htS] until [joinQ] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
    refine k _ _ _ _ _ (atJ_alloc hE hS hz hb (qc := il - vl + 5) (by have := hrb; omega) (by omega) (by omega)
      (by rw [hmcost]; have := hbl; simp only [show il - vl + 1 + 4 = il - vl + 5 by omega] at this ⊢; exact this)
      (by janus_frame) hMF hLF hAp hIn hle hacc h8' hinv' hrg1 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl)
    case _ => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; bv_omega
    all_goals (try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true, h5, h14,
      hM.vt, hM.vn2, hMU.ssh, hMU.sC, hMU.sL, hMU.sP, hM.vlS, hM.vn1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    all_goals first | exact hfs | exact hS.x15 | exact hS.df | rfl | skip
  · have hz0' : 0 < zc := by omega
    have hz48 := ((hpre.zo.2.1 hz0').2.2.2)
    have hpz := hU.pz hz0'
    unfold Apart at hpz
    have hne : zp + 8 * (zc - 1) ≠ P + 8 * (C - 1) := by omega
    janus64_run [m1, m2, m3, hm0', hT1, hT2, hTa, hgS, htS] until [joinQ] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
    refine k _ _ _ _ _ (atJ_alloc hE hS hz hb (qc := il - vl + 5) (by have := hrb; omega) (by omega) (by omega)
      (by rw [hmcost]; have := hbl; simp only [show il - vl + 1 + 4 = il - vl + 5 by omega] at this ⊢; exact this)
      (by janus_frame) hMF hLF hAp hIn hle hacc h8' hinv' hrg1 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl)
    case _ => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; bv_omega
    all_goals (try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true, h5, h14,
      hM.vt, hM.vn2, hMU.ssh, hMU.sC, hMU.sL, hMU.sP, hM.vlS, hM.vn1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    all_goals first | exact hfs | exact hS.x15 | exact hS.df | rfl | skip

end FvModexp.Amd64.DivLarge
