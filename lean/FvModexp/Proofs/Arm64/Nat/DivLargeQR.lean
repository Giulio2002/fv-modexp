import FvModexp.Proofs.Arm64.Nat.DivLargeQRel

/-!
# `divLarge` (arm64): `alias(z, u)` (false) and `q = z.make(m + 1)` reusing `z` (`m + 1 ≤ cap z`), aliasPt → `joinQ`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem qR (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S) (hz : il - vl + 1 ≤ zc)
    (Q : State → Prop)
    (k : ∀ S', AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh zp zc S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hU := hS.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hz40 := hE.pre.zo.1
  have hz0 : 0 < zc := by omega
  have hz48 := ((hE.pre.zo.2.1 hz0).2.2.2)
  have hpz := hU.pz hz0
  unfold Apart at hpz
  have hne : zp + 8 * (zc - 1) ≠ P + 8 * (C - 1) := by omega
  have hM := hS.mem.mem
  have m1 := hM.s3; have m2 := hM.s1; have m3 := hM.mm
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hM.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have hr3 := hS.r3; have hr5 := hS.r5
  janus_run [m1, m2, m3] until [joinQ]
  have he1 : BitVec.ofNat 64 (il - vl) + 1#64 = BitVec.ofNat 64 (il - vl + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb2 := hS.bud2
  refine k _ ⟨rfl, rfl, ?g28, ?g29, ?g18, ?g0, ?g1, ?g2, ?g3, ?g4, ?g5, rfl, ?g12, rfl, he1, hS.mem, hS.ua,
    qarr_reuse hE hS.ua hS.ext2 (fun a n w => hM.fr.accessible a n w) hz, hS.ext2, by omega, hS.sh63, hS.vval,
    hS.vtop, hS.uval⟩
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r28
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r29
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r18
  case g0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r0
  case g1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r1
  case g2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r2
  case g3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r3
  case g4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r4
  case g5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r5
  case g12 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hS.r12

end FvModexp.Arm64.DivLarge
