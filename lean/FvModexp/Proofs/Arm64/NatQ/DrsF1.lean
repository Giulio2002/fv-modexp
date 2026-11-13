import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsFRel
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Arm64.Nat.WinIn

/-! (Q-form copy of Arm64/Nat/DrsF1.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block segment 1: the loop exit and `clear(qhat)` (natdiv.go:860-862)

`f1`: from the loop head `H` with `j ≤ B` (`BLE` → `0x1ba92c`) → `CALL runtime.memclrNoHeapPointers` (`qhat0`,
`8·(B+1)` bytes) → its return `0x1ba938` (`AF1`). Adapted from `b1c`/`b1` (DrsB1).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the final block's `clear(qhat)` call, from the call state `X` -/
theorem f1c (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : j ≤ c.vl / 2) (Q : State → Prop)
    (k : ∀ S', AF1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h1 : X.regs 1 = BitVec.ofNat 64 (8 * (c.vl / 2 + 1)))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rF1) (hm : X.mem = S.mem) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hH.cr
  have hev := hH.ev
  obtain ⟨hce, hsv, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, -, huh, huw, -⟩, ⟨-, -, hvh, hvw, -, -, -⟩, -⟩ :=
    hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, hga, hgr, -, -⟩ := hce'
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hqh := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hqw := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hx : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hEvX : Ev R c s Lk bk X.mem := by rw [hm]; exact hev
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := by rw [hm]; exact hH.fp
  have ht0w := hcr.t0w
  have hdw : c.t0 + 8 * (c.vl / 2 + 1) ≤ s.sp.toNat - c.W ∨ s.sp.toNat + 96 ≤ c.t0 := by
    simp only [win, outside_cons, outside_nil, and_true] at ht0w; omega
  have hn8 : 8 * (c.vl / 2 + 1) < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (hmc Lk bk) (by rw [hpc]) (mc_pre (dst := c.t0) (n := 8 * (c.vl / 2 + 1)) hce
    (by omega) hx X hsp h28 (hEvX.grd hcr) (fun a n w => hEvX.fr.accessible a n w) (by rw [h30]; decide)
    (by rw [h30]; decide) hEvX.inv (by rw [h0, BitVec.toNat_ofNat]; have := hcr.t048; omega)
    (by rw [h1, BitVec.toNat_ofNat]; omega) (hsv.2.2.1 _ _ (by omega)) (by have := hcr.t048; omega)
    (by rw [hEvX.fr.accessible]; exact hcr.t0acc) (hev.ext.held hcr.t0h) hdw) ?_
  intro T hT ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv', hzr⟩ hrg
  subst hs
  have e0 : (X.regs 0).toNat = c.t0 := by rw [h0, BitVec.toNat_ofNat]; have := hcr.t048; omega
  have e1' : (X.regs 1).toNat = 8 * (c.vl / 2 + 1) := by rw [h1, BitVec.toNat_ofNat]; omega
  rw [e0, e1'] at hMF hLF hzr
  rw [show calleeStack X 4096 2 = winA X 4096 24 by simp only [calleeStack, winA]] at hMF
  have hS : ∀ x n, Outside x n (winA s c.W 96) → Outside x n (winA X 4096 24) := fun _ _ ho =>
    winA_in ho hspn (by omega) (by omega) (by omega)
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hst : Outside c.st 24 [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))] := by
    have := hcr.t0st; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  rw [h28] at hinv'
  have hreg' : m.regions = X.mem.regions := by rw [← hrg]; rfl
  have hEvT : Ev R c s Lk bk m := Ev.callN hcr hEvX hMF hLF hS hloc.1 hloc.2 hst hinv' hreg'
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr hEvX hMF hLF hS hst
  have kp : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      m.readLE x n = S.mem.readLE x n := by
    intro x n hh hw' hap
    rw [Held.readLE2 hh hMF hLF (hS _ _ (by simp only [win, winA, outside_cons, outside_nil, and_true] at hw' ⊢; omega))
      (by unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega), hm]
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  unfold Apart at t0q t0u t0v
  have kv := kp _ _ (hx.held hvh) hvw (by unfold Apart; omega)
  have ku : m.readLE c.up (8 * c.u1) = S.mem.readLE c.up (8 * c.u1) :=
    kp _ _ (hx.held (huh.sub (Nat.le_refl _) (by omega))) (huw.of_sub (by omega) (by omega)) (by unfold Apart; omega)
  have kt : m.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega)) (by unfold Apart; omega)
  have kq := kp _ _ (hx.held hqh) hqw (by unfold Apart; omega)
  have hslT : Sl c s m := by
    refine (show Sl c s X.mem by rw [hm]; exact hH.sl).frame hMF ?_
    refine fixOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at ht0w ⊢; omega
  have hbud : c.lo s + c.K s + stkR c.Hq m c.st ≤ bk := by
    have h1 : c.K s ≤ (j / (c.vl / 2) + 1) * c.K s := Nat.le_mul_of_pos_left (c.K s) (Nat.succ_pos _)
    have h2 : c.lo s + (j / (c.vl / 2) + 1) * c.K s + stkR c.Hq X.mem c.st ≤ bk := by rw [hm]; exact hH.bud
    rw [stkR_congr eC]
    omega
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, hcr, hEvT, Fp.hdr hFpX eW eL eC, hslT, kv.trans hH.vk, kt.trans hH.utl,
    limbs_congr kq, hj, hH.li, limbs_congr ku, FvModexp.Expmc.readLE_zeroed hzr, hbud⟩
  · rw [hT]; simp only [h30]
  · exact hsp
  · simp only [retStateX, callRegs, h28]; simp
  · simp only [retStateX, callRegs, h29]; simp
  · simp only [retStateX, callRegs, h18]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the loop exit `j ≤ B` → the final block's `clear(qhat)` → `AF1`** -/
theorem f1 (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : j ≤ c.vl / 2) (Q : State → Prop)
    (k : ∀ S', AF1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hH.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40
  have hpc := hH.pc; have hsp := hH.sp; have h3 := hH.r3; have h0 := hH.r0; have h1 := hH.r1
  have h28 := hH.r28; have h29 := hH.r29; have h18 := hH.r18
  have rn := hH.sl.nn
  have hl3 := lsl3_ofNat (c.vl / 2 + 1) (by omega)
  have hne : (BitVec.ofNat 64 (c.vl / 2 + 1) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hB := lsr1 c.vl (by omega)
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have hacc : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hH.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hjl : j < 2 ^ 63 := by omega
  rcases Nat.lt_or_ge j (c.vl / 2) with hlt | hge
  · have hneg : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2)).getLsbD 63 = true := by
      rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_decide]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hnz : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    janus_run [rn, hl3, hne, hB', hneg, hnz] until [cA "runtime.memclrNoHeapPointers"]
    refine f1c impl R hmc c s Lk bk S j hH hj Q k _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h0
    · exact h28
    · exact h29
    · exact h18
  · have hjB : j = c.vl / 2 := by omega
    have hz : BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = 0#64 := by rw [hjB]; exact BitVec.sub_self _
    janus_run [rn, hl3, hne, hB', hz] until [cA "runtime.memclrNoHeapPointers"]
    refine f1c impl R hmc c s Lk bk S j hH hj Q k _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h0
    · exact h28
    · exact h29
    · exact h18

end FvModexp.Arm64.Q.DivRec
