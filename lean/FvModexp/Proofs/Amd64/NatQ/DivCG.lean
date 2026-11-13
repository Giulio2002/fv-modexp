import FvModexp.Proofs.Amd64.NatQ.DivLG
import FvModexp.Proofs.Amd64.NatQ.DrsStep
import FvModexp.Proofs.Amd64.NatQ.NatMul

set_option autoImplicit false

/-!
# `nat.div` (amd64) CLOSED, Q-form (TIGHT COSTS, top s46): `Q.NatDiv.ensCLG : ExpSlow.DivHypLGQ … (costQ drsCQ)`

amd64 twin of Arm64/NatQ/DivCG.lean. `ensRLG` = `ensDLG` with asm's amd64 `divRecursiveStep` (`Q.DivRec.hyp`, modulo the
`nat.mul` premise `Q.DivRec.MulHypQE`); `ensCLG` = `ensRLG` with divmc's amd64 `Q.NatMul.hypQE` (window `mulWX64`).
Only the live runtime contracts on `Extracted.program.ofImpl impl` remain. `ensCL` (`DivHypLQ`) = `ensCLG.toL`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv

theorem mul_ns : Q.NatMul.names.contains DivLarge.drsFn = false := by decide

theorem mul_code (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 ((Extracted.program.onlySegments Q.NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))

/-- `ensDLG` with asm's `Q.DivRec.hyp`: premise the `nat.mul` summary `Q.DivRec.MulHypQE` on any program `ns` without
the drs, and the live runtime contracts -/
theorem ensRLG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : Q.DivRec.MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLGQ impl R names 41512 112 (costQ drsCQ) :=
  ensDLG impl hap R hgr hmc hwb hmk0 hmv0 hmz0 drsCQ
    (Q.DivRec.hyp impl hap R ns hns hcode hmul hgr hmc hwb hmv0)

/-- **`nat.div`** (amd64), every callee discharged, expmc's `ExpSlow.DivHypLG` form, Q-form (TIGHT COSTS) -/
theorem ensCLG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLGQ impl R names 41512 112 (costQ drsCQ) :=
  ensRLG impl hap R Q.NatMul.names mul_ns (mul_code impl hap)
    (Q.NatMul.hypQE impl hap R hmk0 hgr hmc hmv0 hwb mulWX64) hgr hmc hwb hmk0 hmv0 hmz0

/-- `ensCLG` in the `ExpHyp.DivHypLQ` form -/
theorem ensCL (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypLQ impl R names 41512 112 (costQ drsCQ) :=
  (ensCLG impl hap R hgr hmc hwb hmk0 hmv0 hmz0).toL

end FvModexp.Amd64.Q.NatDiv
