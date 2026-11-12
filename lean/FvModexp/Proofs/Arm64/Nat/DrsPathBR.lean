import FvModexp.Proofs.Arm64.Nat.DrsPathB

/-!
# `divRecursiveStep` (arm64): the run of the `divBasic` path (`n < 40`, `0 < len u`): `pro2b` → CALL → `epiB`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

theorem tN64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`n < divRecursiveThreshold`**: `z.divBasic(stk, u, v)`, return -/
theorem pathB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp.toNat a.vl.toNat a.vc.toNat s) (hc : c = ExpHyp.stackNatCost (stLen s.mem a.st.toNat) (a.vl.toNat + 1))
    (hW : 30608 ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat
      a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat)
    (hN : NatNorm s.mem a.up.toNat ul') (h0 : 0 < ul') (h40 : a.vl.toNat < 40) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp.toNat a.vl.toNat s s') := by
  have hpre' := hpre
  obtain ⟨hce, -, -, -, -, -, huc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcb, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -⟩ := hce
  have hcost : ExpHyp.stackNatCost (stLen s.mem a.st.toNat) (a.vl.toNat + 1) ≤ a.b := hc ▸ hcb
  have hF := hA.fr
  have eu : (BitVec.ofNat 64 ul').toNat = ul' := tN64 (by omega)
  refine pro2b impl (s.regs 30) hA h0 h40 _ fun P' hpc hm hsp hR h28 h29 h18 => ?_
  janus_run until [segAddr Extracted.program DivBasic.fn]
  refine ReachesRet.call_regions (dbsumS impl hap R hgr hmc hwb a.b a.L a.qp a.ql a.qc a.st a.up (BitVec.ofNat 64 ul')
    a.uc a.vp a.vl a.vc) rfl ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 0x1ba4cc : BitVec 64).toNat = 0x1ba4cc := by decide
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom, setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hR 0 (by decide), hA.r0, bv_ofNat_toNat]
    · rw [hR 1 (by decide), hA.r1, bv_ofNat_toNat]
    · rw [hR 2 (by decide), hA.r2, bv_ofNat_toNat]
    · rw [hR 3 (by decide), hA.r3, bv_ofNat_toNat]
    · rw [hR 4 (by decide), hA.r4, bv_ofNat_toNat]
    · rw [hR 5 (by decide), hA.r5]
    · rw [hR 6 (by decide), hA.r6, bv_ofNat_toNat]
    · rw [hR 7 (by decide), hA.r7, bv_ofNat_toNat]
    · rw [hR 8 (by decide), hA.r8, bv_ofNat_toNat]
    · rw [hR 9 (by decide), hA.r9, bv_ofNat_toNat]
  case pre =>
    rw [eu]
    refine db_preS hpre (by omega) ?_ ?_ ?_ ?_ hle hU hN hcost
    · first | exact hF.fr | (rw [hm]; exact hF.fr)
    · first | exact hF.sp | (rw [hsp]; exact hF.sp)
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h28]; exact hF.r28
    · first | exact hF.reg | (rw [hm]; exact hF.reg)
  rw [eu] at hq
  have hsl := fun a' n (h1 : s.sp.toNat - 408 ≤ a') (h2 : a' + n ≤ s.sp.toNat - 392) =>
    db_slot (a := a') (n := n) hpre (by omega) (by exact hF.fr) (by exact hF.sp) hle hq h1 h2
  refine epiB impl s T ?pc ?sp ?r28 ?r18 ?lr ?fp (by omega) (by omega) hal ?acc hE.1 hE.2.1 _
    fun s' ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, e2, e3, e4⟩, ?post⟩
  case pc => rw [hT]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case sp => rw [f1]; exact hF.sp
  case r28 => rw [f2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h28]; exact hF.r28
  case r18 => rw [f4]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h18]; exact hF.r18
  case lr => rw [(hsl _ 8 (by omega) (by omega)).1]; exact hF.lr
  case fp => rw [(hsl _ 8 (by omega) (by omega)).1]; exact hF.fp
  case acc =>
    rw [(hsl (s.sp.toNat - 400) 8 (by omega) (by omega)).2]
    exact Memory.accessible_mono _ (Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  case post =>
    have := db_postS hpre (by omega) (by exact hF.fr) (by exact hF.sp)
      (by simp only [setReg_apply, ↓reduceIte]; rw [h28]; exact hF.r28) hle hU hc hq
    unfold DrsPostW ExpHyp.RtPost at this ⊢; rw [e5]; exact this

end FvModexp.Arm64.DivRec
