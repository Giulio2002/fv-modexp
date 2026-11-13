import FvModexp.Proofs.Arm64.NatQ.DivRel

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivBig.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `u ≥ v` (`len v ≥ 2`): from `AtC` (`cmp ≥ 0`, `stk ≠ nil`) to `divLarge`'s entry (natdiv.go:538-543)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem big1 (impl : List Segment) {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State} {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c) (hst : st ≠ 0)
    (hal : s.sp.toNat % 16 = 0) (hb' : 41504 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true) (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivLarge.fn) → X.sp = s.sp - 240#64 →
      X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 248#64 → X.regs 18 = s.regs 18 →
      X.regs 30 = BitVec.ofNat 64 retL →
      X.regs 0 = BitVec.ofNat 64 zp → X.regs 1 = BitVec.ofNat 64 zl → X.regs 2 = BitVec.ofNat 64 zc →
      X.regs 3 = BitVec.ofNat 64 st → X.regs 4 = BitVec.ofNat 64 z2 → X.regs 5 = BitVec.ofNat 64 z2l →
      X.regs 6 = BitVec.ofNat 64 z2c → X.regs 7 = BitVec.ofNat 64 u → X.regs 8 = BitVec.ofNat 64 ul →
      X.regs 9 = BitVec.ofNat 64 uc → X.regs 10 = BitVec.ofNat 64 v → X.regs 11 = BitVec.ofNat 64 vl →
      X.regs 12 = BitVec.ofNat 64 vc →
      MemFrame S.mem X.mem [(s.sp.toNat - 122, s.sp.toNat - 121)] → X.mem.regions = S.mem.regions →
      X.mem.readLE (s.sp.toNat - 122) 1 = 0 →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hS.mf.accessible]; exact hw
  have m1 := hS.s1; have m2 := hS.s2; have m3 := hS.s3; have m4 := hS.s4; have m5 := hS.s5; have m6 := hS.s6
  have m7 := hS.s7; have m8 := hS.s8; have m9 := hS.s9; have m10 := hS.s10; have m11 := hS.s11; have m12 := hS.s12
  have m13 := hS.s13
  have hst64 : st < 2 ^ 64 := by rw [← m4]; exact Memory.readLE_lt _ _ _
  have hst' : (BitVec.ofNat 64 st = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hc' : (c = 0 ∨ c = 1) := by omega
  clear hS
  rcases hc' with rfl | rfl
  all_goals janus_run [hr0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, hst'] until
    [segAddr Extracted.program DivLarge.fn]
  all_goals refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (simp only [Memory.regions_writeLE]; done) | (janus_frame; done) | janus_simp

end FvModexp.Arm64.Q.NatDiv
