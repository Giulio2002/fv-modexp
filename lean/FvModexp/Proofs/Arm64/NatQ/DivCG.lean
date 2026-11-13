import FvModexp.Proofs.Arm64.NatQ.DivLG
import FvModexp.Proofs.Arm64.NatQ.DrsStep
import FvModexp.Proofs.Arm64.NatQ.MulHypD

set_option autoImplicit false

/-!
# `nat.div` (arm64) CLOSED, Q-form (TIGHT COSTS, asm s39): `Q.NatDiv.ensCLG : ExpSlow.DivHypLGQ … (costQ drsCQ)`

Q twin of Arm64/Nat/DivCG.lean. `ensRLG` = `ensDLG` with the Q `divRecursiveStep` (`Q.DivRec.hyp`, modulo the
`nat.mul` premise `Q.DivRec.MulHypQE`); `ensCLG` = `ensRLG` with `Q.DivRec.mulHyp` (NatQ/MulHypD: divmc's `Q.NatMul.ens`
in the premise's shape, without the old `nat.mul` chain's import). Only the live runtime
contracts on `Extracted.program.ofImpl impl` remain. `ensCL` (`DivHypLQ`) = `ensCLG.toL`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv

theorem mul_ns : NatMul.names.contains DivRec.fn = false := by decide

theorem mul_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn ((Extracted.program.onlySegments NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))

theorem ensRLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivRec.fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : Q.DivRec.MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX)
    (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLGQ impl R names 41504 112 (costQ drsCQ) :=
  ensDLG impl hap R hgr hmc hwb hmk0 hmv0 hmz0 drsCQ
    (Q.DivRec.hyp impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmv0)

/-- **`nat.div`** (arm64), every callee discharged, expmc's `ExpSlow.DivHypLG` form, Q-form (TIGHT COSTS) -/
theorem ensCLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLGQ impl R names 41504 112 (costQ drsCQ) :=
  ensRLG impl hap R NatMul.names mul_ns (mul_code impl hap)
    (Q.DivRec.mulHyp impl hap R hmk0 hgr hmc hmv0 hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmk0 hmv0
    hmz0

/-- `ensCLG` in the `ExpHyp.DivHypLQ` form -/
theorem ensCL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypLQ impl R names 41504 112 (costQ drsCQ) :=
  (ensCLG impl hap R hgr hmc hwb hmk0 hmv0 hmz0).toL

end FvModexp.Arm64.Q.NatDiv
