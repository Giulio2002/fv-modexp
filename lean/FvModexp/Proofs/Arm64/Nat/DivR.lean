import FvModexp.Proofs.Arm64.Nat.Div
import FvModexp.Proofs.Arm64.Nat.DrsStep

/-!
# `nat.div` (arm64) with `divLarge` AND `divRecursiveStep` discharged (MILESTONE, asm s30)

`ensR`: `NatDiv.ensD` with `dc := drsC` and `hD := DivRec.hyp` — `nat.div`'s `Ensures` (`ExpHyp.DivPre` /
`ExpHyp.DivPost`, window `41504 / 112`, budget `NatDiv.cost drsC`) modulo only the `nat.mul` premise `MulHypXE`
(divmc's export, on any program `ns` without `divRecursiveStep` inside `LibDrs`) and the live runtime contracts.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatDiv

/-- **`nat.div`** (arm64), complete modulo the `nat.mul` premise -/
theorem ensR (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivRec.fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : DivRec.MulHypXE impl R ns stkM aboveM mulC) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHyp impl R names 41504 112 (cost DivRec.drsC) :=
  fun b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    ensD impl hap R hgr hmc hwb hmk0 hmv0 hmz0 DivRec.drsC
      (DivRec.hyp impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmv0) b L z zl zc st z2 z2l z2c u ul uc v vl vc

/-- **`nat.div`** (arm64), complete modulo the `nat.mul` premise, `StackBackL` form (`ExpHyp.DivHypL`) -/
theorem ensRL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivRec.fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : DivRec.MulHypXE impl R ns stkM aboveM mulC) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypL impl R names 41504 112 (cost DivRec.drsC) :=
  fun b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    ensDL impl hap R hgr hmc hwb hmk0 hmv0 hmz0 DivRec.drsC
      (DivRec.hyp impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmv0) b L z zl zc st z2 z2l z2c u ul uc v vl vc

end FvModexp.Arm64.NatDiv
