import FvModexp.Proofs.Amd64.NatQ.DivLargeDBR

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeDBS.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): the run `joinQ` → `divBasic`'s entry (natdiv.go:623-627)

`+0x58f`: `q` stored at `RSP - 64 … - 48`; `CMPQ divRecursiveThreshold, R11; JG +0x649` (taken: `n < 40`); `+0x649`:
`v = (t, vl, vl)` at `RSP' + 0 … + 16` (`RSP' = RSP - 304`), `RAX, RBX, RCX = q`, `RDI = stk` (from `RSP + 80`),
`RSI, R8, R9 = u`; `CALL divBasic` (return address `+0x676` at `RSP - 312`) → `db2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `n < divRecursiveThreshold`: from `joinQ` to `divBasic`'s entry, then the call -/
theorem db (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (dc : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (hv40 : vl < 40)
    (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hM := hS.mem.mem
  have m1 := hM.s4
  obtain ⟨g1, g2, hgw⟩ := Mem.thr hE hM
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hE.pre.ce
  simp only [regSP] at hb' ha hw
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hM.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hr0 := hS.r0; have hr1 := hS.r1; have hr6 := hS.r6; have hr7 := hS.r7; have hr8 := hS.r8; have hr9 := hS.r9
  have hr11 := hS.r11; have hr12 := hS.r12; have hr13 := hS.r13; have hr15 := hS.r15
  have hti := FvModexp.toInt_small (BitVec.ofNat 64 vl) (by simp; omega)
  janus64_run [m1, g1, hti, BitVec.msb_eq_decide] until [segAddr Extracted.program DivBasic.fn]
  have hqc := hS.qa.c40; have hcap := hS.ua.cap; have hq48 := hS.qa.p48; have ht48 := hl.t48
  refine db2 impl hap R hgr hmc hwb dc b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS _
    ?gpc ?gsp ?grd ?g5 ?g14 ?gfs ?gx ?gdf ?g0 ?g3 ?g7 ?g6 ?g8 ?g9 (by simp only [callWs]; janus_frame)
    ?q0 ?q1 ?q2 ?vS ?lS ?greg Q k
  case greg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hS.reg
  all_goals (try janus64_simp)
  all_goals first
    | exact h5 | exact h14 | exact hfs | exact hx15 | rfl | bv_omega
    | (simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Nat.reducePow]; omega)
    | skip

end FvModexp.Amd64.Q.DivLarge
