import FvModexp.Proofs.Arm64.Nat.DivLargeQRel

/-!
# `divLarge` (arm64): `q = z.make(m + 1)` allocating (`cap z < m + 1`), `m ≠ 0`: `makeslice(Word, m + 1, m + 5)`,
from the allocation branch (`fn + 0x2fc`) to `joinQ`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)
open FvModexp.Arm64.DivBasic (LiveFrame.trans')

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

/-- the allocation branch of `z.make(m + 1)` -/
abbrev allocQ : Nat := segAddr Extracted.program fn + 0x2fc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem qAm (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S) (hz : zc < il - vl + 1)
    (hm0 : il - vl ≠ 0) (hb : makeCost (il - vl + 1) ≤ bk)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 allocQ) (hsp : X.sp = s.sp - 304#64) (h28 : X.regs 28 = s.regs 28)
    (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h13 : X.regs 13 = BitVec.ofNat 64 (il - vl)) (h15 : X.regs 15 = BitVec.ofNat 64 (il - vl + 1))
    (hm : X.mem = S.mem) (Q : State → Prop)
    (k : ∀ S' Lq bq qp qc, AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hpre := hE.pre
  have hU := hS.ua
  have hMU := hS.mem
  have hM := hMU.mem
  obtain ⟨hal, hb', ha, hw⟩ := hpre.ce.2.1
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hSacc]; exact hw
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  have hd := hpre.ce.2.2.1
  have hsv := hpre.sv
  obtain ⟨hty, hwt, hWr⟩ := Mem.wordK hE hM
  have hk1' : il - vl + 1 ≠ 1 := by omega
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, il - vl + 1, il - vl + 5] := hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (il - vl + 1) = allocCost (8 * (il - vl + 1 + 4)) := by
    unfold makeCost makeCap; rw [if_neg hk1']
  have hbl := blockSize_le_allocCost (8 * (il - vl + 1 + 4)) true
  have hbs : blockSize (8 * (il - vl + 1 + 4)) true ≤ bk := by omega
  have hinv2 := hM.inv
  have hga := hpre.ce.2.2.2.2.1
  have hgr := hpre.ce.2.2.2.2.2.1
  unfold Apart at hwt hga
  have hgS := hMU.grd
  obtain ⟨hg1, hg2, hg3⟩ := hpre.ce.1
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S.mem.readLE 2641088 8 = s.mem.readLE 2641088 8 := hWr _ _ (by omega) (by omega)
  have hT2 : S.mem.readLE 2641096 8 = s.mem.readLE 2641096 8 := hWr _ _ (by omega) (by omega)
  have hTa : S.mem.accessible 2641088 16 false = s.mem.accessible 2641088 16 false := hSacc _ _ _
  have hLs1 := lsep_of hE hS.ext2
  have hc1 := hE.c1len
  have hw1h : Held R Lk w1 (8 * c1) := hS.ext2.held (hE.w1live (by simp only [StackNat.rnd] at hc1; omega)).2.1
  have m1 := hM.vn1; have m2 := hM.vn2; have m3 := hMU.sC; have m4 := hMU.sL; have m5 := hMU.sP; have m6 := hMU.ssh
  have m7 := hM.s12; have m8 := hM.vt
  have he5 : BitVec.ofNat 64 (il - vl) + 5#64 = BitVec.ofNat 64 (il - vl + 5) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hne : (BitVec.ofNat 64 (il - vl) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [hm, he5, hne, hT1, hT2, hTa, hgS] until [joinQ] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
  have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
  have hptr : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hS1 : MemFrame S.mem ((S.mem.writeLE (s.sp.toNat - 144) 8 (il - vl + 1)).writeLE (s.sp.toNat - 184) 8
      (il - vl + 5)) [(s.sp.toNat - 144, s.sp.toNat - 136), (s.sp.toNat - 184, s.sp.toNat - 176)] := by janus_frame
  have hf : MemFrame S.mem m (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine (mfTrans hS1 hMF).mono fun a n ho => ?_
    have ho' := ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho'
    obtain ⟨⟨⟨hrt, hsc⟩, -⟩, -⟩ := ho'
    simp only [outside_append, outside_cons, outside_nil, and_true]
    repeat' apply And.intro
    all_goals first | exact hrt | omega
  have keep : ∀ a n, Held R Lk a n → (a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a) →
      m.readLE a n = S.mem.readLE a n := by
    intro a n hh hw0
    rw [← hS1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rcases hh with hi | ho
    · exact hLF.readLE a n hi trivial
    · exact hMF.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho, by omega, by omega⟩)
  have hlf : LiveFrame S.mem m L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    ⟨fun a n hin _ => by
      have hw0 : a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a := by
        obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
      exact keep a n (Or.inl (hS.ext2.inRanges_old (hE.ext.inRanges_old hin))) hw0⟩
  have hacc2 : ∀ a n w, m.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hMF.accessible, hS1.accessible]
  have hx1 : LiveExt R Lk (Lk ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (il - vl + 5)) true)]) :=
    LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hblk : blockSize (8 * (il - vl + 5)) true ≤ makeCost (il - vl + 1) := by rw [hmcost]; exact hbl
  have hth : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  have htv : natVal m t vl = natVal S.mem t vl := keep _ _ hth hl.tw
  have hpv : natVal m P (il + 1) = natVal S.mem P (il + 1) :=
    keep _ _ (hU.pheld.sub (by omega) (by have := hU.cap; omega)) (by have := hU.pw; have := hU.cap; omega)
  have htt : m.readLE (t + 8 * (vl - 1)) 8 = S.mem.readLE (t + 8 * (vl - 1)) 8 :=
    keep _ _ (hth.sub (by omega) (by omega)) (by have := hl.tw; omega)
  have hb2 := hS.bud2
  refine k _ (Lk ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (il - vl + 5)) true)]) (bk - blockSize (8 * (il - vl + 5)) true)
    ptr.toNat (il - vl + 5) ⟨rfl, rfl, ?g28, ?g29, ?g18, ?g0, ?g1, ?g2, ?g3, ?g4, ?g5, ?g6, ?g12, ?g14, ?g15,
    MemU.frame hE hMU hU hf hlf hinv', UArr.live (UArr.frame hU hacc2) hx1,
    (qarr_alloc hE hU hS.ext2 hz hAp hIn hle hacc h8' (by omega) (by omega) (by omega)
      hw1h).frame hacc2,
    LiveExt.trans hS.ext2 hx1, by omega, hS.sh63, by rw [htv]; exact hS.vval, by rw [htt]; exact hS.vtop,
    by rw [hpv]; exact hS.uval, by simp only [Memory.regions_writeLE] at hrg1 ⊢; first | (rw [hrg1]; exact hS.reg) | (rw [hrg1, hm]; exact hS.reg)⟩
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply, true_or, or_true, if_true, h28]
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply, true_or, or_true, if_true, h29]
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply, true_or, or_true, if_true, h18]
  case g0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m8]
  case g1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m1]
  case g2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m2]
  case g3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m3]
  case g4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m4]
  case g5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m5]
  case g6 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g12 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m7]
  case g14 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case g15 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]

end FvModexp.Arm64.DivLarge
