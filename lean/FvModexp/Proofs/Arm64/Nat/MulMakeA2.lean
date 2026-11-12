import FvModexp.Proofs.Arm64.Nat.MulMakeAP

set_option autoImplicit false

/-!
# `nat.mul` (arm64), `make_alloc`: the `makeslice(Word, m + n, m + n + 4)` call at `0x1baf48` (`AA`) → the join
`0x1baf70` (`Core`, `JoinAt`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (apart_of_held)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem alloc_call (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMul.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp _zl zc st xp xl xc yp yl yc : BitVec 64) (s S : State) (hA : AA s S W st xp xl xc yp yl yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hround, hsize, hnoscan⟩ := mfacts hpre hA rfl rfl
  have hc := mcall_pre hpre hy2 hyx hA rfl rfl
  have hpre' := hpre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, -, hxl12, -, hxh, -⟩, ⟨hylc, -, hyl12, -, hyh, -⟩, -, -⟩, -, -, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hxh' := (hxh (by omega)).1
  have hyh' := (hyh (by omega)).1
  have hmc : makeB (xl.toNat + yl.toNat) = allocCost (8 * (xl.toNat + yl.toNat + 4)) := rfl
  obtain ⟨hpc, hr30, r0, r1, r2, hsp, hg, hfp, h18, mlr, mfp, m120, m96, m288, m296, m304, m312, m320, m328, m336, hF0,
    hreg⟩ := hA
  have hsp' : S.sp.toNat = s.sp.toNat - 256 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  clear hxh hyh
  refine ReachesRet.call_regions (hmk.pos L b) hpc hc ?_
  intro S1 hpc1 ⟨ptr, junk, f1, v1, m, ex1, ep1, hs1, hMF, hLF, ⟨hobj, hAp⟩, hapS, hinv'⟩ hreg1
  subst hs1
  clear hc
  simp only [makesliceObj, Fresh, hsize, hnoscan] at hobj
  rw [hround] at hAp hinv'
  rw [hg] at hinv'
  obtain ⟨hIn, hle, hacc, h8, -, -, hsz⟩ := hobj
  simp only [calleeStack, hsp'] at hMF hapS
  have hrd : ∀ a, (s.sp.toNat - 264 ≤ a ∧ a + 8 ≤ s.sp.toNat - 248) ∨ (s.sp.toNat - 160 ≤ a ∧ a + 8 ≤ s.sp.toNat + 88) →
      m.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have q120 := (hrd _ (by omega)).trans m120
  have q96 := (hrd _ (by omega)).trans m96
  have q288 := (hrd _ (by omega)).trans m288
  have q296 := (hrd _ (by omega)).trans m296
  have q304 := (hrd _ (by omega)).trans m304
  have q312 := (hrd _ (by omega)).trans m312
  have q320 := (hrd _ (by omega)).trans m320
  have q328 := (hrd _ (by omega)).trans m328
  have q336 := (hrd _ (by omega)).trans m336
  have qlr := (hrd _ (by omega)).trans mlr
  have qfp := (hrd _ (by omega)).trans mfp
  clear hrd m120 m96 m288 m296 m304 m312 m320 m328 m336 mlr mfp
  janus_run [hsp', hr30, hreg, q120, q96, q288, q296, q304, q312, q320, q328, q336] until [0x1baf70]
  all_goals
    refine hK ptr.toNat (xl.toNat + yl.toNat + 4) _ _ _ (Core.win (core_alloc (c := xl.toNat + yl.toNat + 4) hpre hF0
        ?qcs hLF hMF hAp hIn hle hacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
      ⟨?jpc, ?j0, ?j1, ?j2, ?j3, ?j4, ?j5, ?j6, ?j7, ?j8, ?j9, ?jsp, ?jg, ?jfp, ?j18, ?jlr, ?jmfp, ?j120, ?j296,
        ?j304, ?j312, ?j320, ?j328, ?j336, ?jreg,
        apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs2),
        apart_of_held (hyh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs3)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs4), ?qnx, ?qny⟩
    case qnx =>
      have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qny =>
      have := apart_of_held hyh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qs1 => omega
    case qs2 => omega
    case qs3 => omega
    case qs4 => omega
    case hF2 => exact MemFrame.refl _ _
    case qcs => intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case q1 => omega
    case q2 => rw [hmc]; exact blockSize_le_allocCost _ true
    case q3 => omega
    case q4 => omega
    case q5 => omega
    case jpc => rfl
    case jsp => rfl
    case j0 => simp only [setReg_apply, callRegs_apply]; simp
    case j1 => simp only [setReg_apply, callRegs_apply]; simp
    case j2 => simp only [setReg_apply, callRegs_apply]; simp
    case j3 => simp only [setReg_apply, callRegs_apply]; simp
    case j4 => simp only [setReg_apply, callRegs_apply]; simp
    case j5 => simp only [setReg_apply, callRegs_apply]; simp
    case j6 => simp only [setReg_apply, callRegs_apply]; simp
    case j7 => simp only [setReg_apply, callRegs_apply]; simp
    case j8 => simp only [setReg_apply, callRegs_apply]; simp
    case j9 => simp only [setReg_apply, callRegs_apply]; simp
    case jg => simp only [setReg_apply, callRegs_apply]; simpa using hg
    case jfp => simp only [setReg_apply, callRegs_apply]; simpa using hfp
    case j18 => simp only [setReg_apply, callRegs_apply]; simpa using h18
    case jlr => exact qlr
    case jmfp => exact qfp
    case j120 => exact q120
    case j296 => exact q296
    case j304 => exact q304
    case j312 => exact q312
    case j320 => exact q320
    case j328 => exact q328
    case j336 => exact q336
    case jreg => exact hreg1.trans hreg

end FvModexp.Arm64.NatMul
