import FvModexp.Proofs.Arm64.Nat.DivLargeDB

/-!
# `divLarge` (arm64): the `divBasic` call (`fn + 0x44c`) and the run `joinQ` → call (natdiv.go:623-627)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

theorem tN64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `divBasic`'s entry: the call, then `AtD` -/
theorem db2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (dc : Nat → Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (X : State)
    (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivBasic.fn)) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x450))
    (hr0 : X.regs 0 = BitVec.ofNat 64 qp) (hr1 : X.regs 1 = BitVec.ofNat 64 (il - vl + 1))
    (hr2 : X.regs 2 = BitVec.ofNat 64 qc) (hr3 : X.regs 3 = BitVec.ofNat 64 st) (hr4 : X.regs 4 = BitVec.ofNat 64 P)
    (hr5 : X.regs 5 = BitVec.ofNat 64 (il + 1)) (hr6 : X.regs 6 = BitVec.ofNat 64 C)
    (hr7 : X.regs 7 = BitVec.ofNat 64 t) (hr8 : X.regs 8 = BitVec.ofNat 64 vl) (hr9 : X.regs 9 = BitVec.ofNat 64 vl)
    (hF : MemFrame S.mem X.mem [(s.sp.toNat - 64, s.sp.toNat - 40)])
    (hq0 : X.mem.readLE (s.sp.toNat - 64) 8 = qp) (hq1 : X.mem.readLE (s.sp.toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE (s.sp.toNat - 48) 8 = qc) (hreg : X.mem.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hcap := hS.ua.cap; have hc40 := hS.ua.c40; have hqcap := hS.qa.cap; have hq40 := hS.qa.c40
  have e0 : (BitVec.ofNat 64 qp).toNat = qp := tN64 (by have := hS.qa.p48; omega)
  have e1 : (BitVec.ofNat 64 (il - vl + 1)).toNat = il - vl + 1 := tN64 (by omega)
  have e3 : (BitVec.ofNat 64 st).toNat = st := tN64 (by have := hl.st48; omega)
  have e4 : (BitVec.ofNat 64 P).toNat = P := tN64 (by have := hS.ua.p48; omega)
  have e5 : (BitVec.ofNat 64 (il + 1)).toNat = il + 1 := tN64 (by omega)
  have e6 : (BitVec.ofNat 64 C).toNat = C := tN64 (by omega)
  have e7 : (BitVec.ofNat 64 t).toNat = t := tN64 (by have := hl.t48; omega)
  have e8 : (BitVec.ofNat 64 vl).toNat = vl := tN64 (by omega)
  have hcost : stackNatCost (stLen s.mem st + StackNat.rnd vl) (vl + 1) ≤ bq := by
    have := bud_div hE hS.bud3; omega
  have hpre := db_pre hE hS X hsp h28 hF hreg hcost
  have hsum := dbsum impl hap R hgr hmc hwb bq Lq (BitVec.ofNat 64 qp) (BitVec.ofNat 64 (il - vl + 1))
    (BitVec.ofNat 64 qc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 P) (BitVec.ofNat 64 (il + 1)) (BitVec.ofNat 64 C)
    (BitVec.ofNat 64 t) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vl)
  have e30 : (X.regs 30).toNat = 1809824 := by rw [h30]; decide
  refine ReachesRet.call_regions hsum hpc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [e30]; exact raL impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]
    exact ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, trivial⟩
  case pre =>
    show DivBasic.Pre R bq Lq _ _ _ _ _ _ _ _ X
    rw [e0, e1, e3, e4, e5, e6, e7, e8]; exact hpre
  show ReachesRet _ _ T Q
  rw [e0, e1, e3, e4, e5, e7, e8] at hq
  obtain ⟨hqv, hrv, L', b', hx, hb, hinv, hSB, hMF, hLF⟩ := hq
  have hqn : DivBasic.qn (il - vl + 1) (il + 1) vl = il - vl + 1 := by
    simp only [DivBasic.qn]; rw [if_pos (by omega)]; omega
  have hqv' := hqv (by omega)
  rw [hqn] at hqv'
  simp only [DivBasic.ws, hqn] at hMF hLF
  rw [h28] at hinv
  exact k _ _ _ _ T (dbPost hE hS hsp hF hq0 hq1 hq2 hreg (by rw [hT, h30]) (by rw [f1, hsp]) (by rw [f2, h28])
    (by rw [f3, h29]) (by rw [f4, h18]) hrg hqv' hrv hx hb hinv hSB
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hMF) hLF)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `n < divRecursiveThreshold`: from `joinQ` (q stored, threshold loaded, `BLT`) to `divBasic`'s entry -/
theorem db (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (dc : Nat → Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (hv40 : vl < 40)
    (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hM := hS.mem.mem
  have m1 := hM.s4
  obtain ⟨g1, g2⟩ := Mem.glob hE hM
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hM.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr3 := hS.r3; have hr4 := hS.r4; have hr5 := hS.r5
  have hr6 := hS.r6; have hr12 := hS.r12; have hr14 := hS.r14; have hr15 := hS.r15
  have hgw : 7147136 + 32 ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ 7147136 := by
    have := hE.pre.gl.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at this; exact this
  janus_run [m1, g1] until [segAddr Extracted.program DivBasic.fn]
  have hqc := hS.qa.c40; have hcap := hS.ua.cap; have hq48 := hS.qa.p48
  refine db2 impl hap R hgr hmc hwb dc b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS _
    rfl rfl ?g28 ?g29 ?g18 rfl ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 (by janus_frame) ?q0 ?q1 ?q2 ?greg Q k
  case greg => simp only [Memory.regions_writeLE]; exact hS.reg
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
  case g0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g6 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g7 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g8 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g9 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals
    simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
    omega

end FvModexp.Arm64.DivLarge
