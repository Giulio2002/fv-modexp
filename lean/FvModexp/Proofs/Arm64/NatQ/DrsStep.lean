import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsLoop
import FvModexp.Proofs.Arm64.NatQ.DrsFL
import FvModexp.Proofs.Arm64.NatQ.DrsEntry
import FvModexp.Proofs.Arm64.NatQ.DrsPathBR
import FvModexp.Proofs.Arm64.NatQ.DrsSN

/-! (Q-form copy of Arm64/Nat/DrsStep.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64): the whole function (natdiv.go:750-892) by induction on `len v`

* `drs_step`: one member case of `Summary.induction_mutual` (measure `μ = len v`): `entry` (`u.norm()`, `v.norm()`),
  then `len u = 0` (`pathA`: `clear(z)`), `n < 40` (`pathB`: `divBasic`), `len u < n` (`pathC`), and the big path
  `pro2d` → `snH` (`stk.nat(B + 1)`) → `loop` (the wide-digit loop, recursive calls via the induction hypothesis) →
  `final` (the final block, the deferred `stk.restore`, the return).
* `sum`: the summary for every argument record (`Summary.induction_mutual`).
* **`hyp`**: `DivLarge.DrsHyp impl R drsC` — the premise of `divLarge` / `nat.div` — modulo the `nat.mul` premise
  (`MulHypXE` on any program `ns` without `divRecursiveStep` inside `LibDrs`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW DrsHypQ)

/-- **one member case** of the induction on `len v` -/
theorem drs_step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (n : Nat) (ih : ∀ a, IH impl R n a) (a : Args) :
    Summary (P impl) 0x1ba3a0 (fun s => preOf R a s ∧ μ a s = n) (postOf R a) := by
  intro s hpc ⟨⟨hE, hW, hpre⟩, hμ⟩
  have hn : a.vl.toNat = n := hμ
  subst hn
  have hWg := drsW_ge a.vl.toNat
  refine entry impl R a s hpc hE hpre (by omega) _ fun P ul' hA hle hU hN => ?_
  rcases Nat.eq_zero_or_pos ul' with h0 | h0
  · subst h0; exact pathA impl R hmc' a s hE hpre (by omega) P hA hU
  by_cases h40 : a.vl.toNat < 40
  · exact pathB impl hap R hgr hmc hwb a s hE hpre (drsCQ_small h40) (by omega) P ul' hA hle hU hN h0 h40
  have h40' : 40 ≤ a.vl.toNat := by omega
  by_cases hlt : ul' < a.vl.toNat
  · exact pathC impl R a s hE hpre (by omega) P ul' hA hU h0 h40' hlt
  refine pro2d impl (s.regs 30) hA h0 h40' (by omega) a.qp.isLt a.ql.isLt a.qc.isLt a.st.isLt a.up.isLt a.uc.isLt
    a.vp.isLt a.d.isLt _ fun P' hN0 => ?_
  refine snH impl hap R hgr hmc hwb a s hE hpre hW P' ul' hN0 hle hU hN h40' (by omega) _ fun t0 L1 Lk bk S hH => ?_
  exact loop impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmc' hmv (cOf a ul' t0 L1) ih s _
    (fun L' b' S' j' hj hH' =>
      final impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmc' hmv (cOf a ul' t0 L1) ih s L' b' S' j' hj hH')
    _ _ Lk bk S (Nat.le_refl _) hH

/-- **`divRecursiveStep`'s summary** for every argument record (on `LibDrs`) -/
theorem sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ∀ a, Summary (P impl) 0x1ba3a0 (preOf R a) (postOf R a) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibDrs.names
  rw [← LibDrs.eq_only] at hc
  have hmc' : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R :=
    MemclrNoHeapPointersLive.of_codeIn hc hmc
  exact Summary.induction_mutual (entry := fun _ => 0x1ba3a0) μ fun n ih a =>
    drs_step impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmc' hmv n ih a

/-- **`divRecursiveStep` (arm64)**: `DivLarge.DrsHyp impl R drsC` (the premise of `divLarge` / `nat.div`), modulo the
`nat.mul` premise `MulHypXE` (divmc's export) and the live runtime contracts -/
theorem hyp (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    DrsHypQ impl R drsCQ := by
  intro H b L qp ql qc st up ul uc vp vl vc d
  rw [show DivLarge.drsNames = LibDrs.names from rfl, ← LibDrs.eq_only, entry_drs]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  have hv9 := hpre.2.2.2.2.2.2.2.2.2.2.1.1
  refine Summary.returns (sum impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmv ⟨H, b, L, 40960, qp, ql, qc, st, up, ul, uc,
    vp, vl, vc, d⟩) hret h_pc h_lr ⟨⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10⟩,
      drsW_le hv9, hpre⟩ fun s' h => by unfold postOf at h; obtain ⟨⟨a, b, c, d⟩, hq⟩ := h; exact ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Q.DivRec
