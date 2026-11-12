import FvModexp.Proofs.Arm64.Nat.DivLargeQR
import FvModexp.Proofs.Arm64.Nat.DivLargeQA1

/-!
# `divLarge` (arm64): `alias(z, u)` and `q = z.make(m + 1)` (natdiv.go:620-623), from the alias test to `joinQ`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem qSeg (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S)
    (hb : makeCost (il - vl + 1) ≤ bk) (Q : State → Prop)
    (k : ∀ S' Lq bq qp qc, AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  by_cases hz : il - vl + 1 ≤ zc
  · exact qR impl R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh hE S hS hz Q
      (fun S' h => k S' Lk bk zp zc h)
  have hz' : zc < il - vl + 1 := by omega
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hU := hS.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hz40 := hE.pre.zo.1
  have hM := hS.mem.mem
  have m1 := hM.s3; have m2 := hM.s1; have m3 := hM.mm
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hM.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have hr3 := hS.r3; have hr5 := hS.r5
  have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have he1 : BitVec.ofNat 64 (il - vl) + 1#64 = BitVec.ofNat 64 (il - vl + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have kA : ∀ X : State, X.pc = BitVec.ofNat 64 allocQ → X.sp = s.sp - 304#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 312#64 → X.regs 18 = s.regs 18 → X.regs 13 = BitVec.ofNat 64 (il - vl) →
      X.regs 15 = BitVec.ofNat 64 (il - vl + 1) → X.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
    intro X x1 x2 x3 x4 x5 x6 x7 x8
    by_cases hm0 : il - vl = 0
    · exact qA1 impl R hmk b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh hE S hS hz' hm0 hb X
        x1 x2 x3 x4 x5 x6 x7 x8 Q k
    · exact qAm impl R hmk b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh hE S hS hz' hm0 hb X
        x1 x2 x3 x4 x5 x6 x7 x8 Q k
  by_cases hz0 : zc = 0
  · subst hz0
    janus_run [m1, m2, m3, he1] until [allocQ]
    refine kA _ rfl rfl ?g28 ?g29 ?g18 ?g13 ?g15 rfl
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]
  · have hz0' : 0 < zc := by omega
    have hz48 := ((hE.pre.zo.2.1 hz0').2.2.2)
    have hpz := hU.pz hz0'
    unfold Apart at hpz
    have hne : zp + 8 * (zc - 1) ≠ P + 8 * (C - 1) := by omega
    janus_run [m1, m2, m3, he1] until [allocQ]
    refine kA _ rfl rfl ?g28 ?g29 ?g18 ?g13 ?g15 rfl
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]

end FvModexp.Arm64.DivLarge
