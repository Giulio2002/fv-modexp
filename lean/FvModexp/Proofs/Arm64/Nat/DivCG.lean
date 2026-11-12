import FvModexp.Proofs.Arm64.Nat.DivC
import FvModexp.Proofs.Arm64.Nat.DivLG

set_option autoImplicit false

/-!
# `nat.div` (arm64) CLOSED in expmc's `ExpSlow.DivHypLG` form (asm s35)

`ensRLG` = `ensDLG` with `DivRec.hyp` (modulo the `nat.mul` premise); `ensCLG` = `ensRLG` with divmc's
`NatMul.hypXE` — only the live runtime contracts on `Extracted.program.ofImpl impl` remain (as `ensCL`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatDiv

theorem ensRLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivRec.fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : DivRec.MulHypXE impl R ns stkM aboveM mulC) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLG impl R names 41504 112 (cost DivRec.drsC) :=
  ensDLG impl hap R hgr hmc hwb hmk0 hmv0 hmz0 DivRec.drsC
    (DivRec.hyp impl hap R ns hns hcode hmul hk ha hgr hmc hwb hmv0)

/-- **`nat.div`** (arm64), every callee discharged, expmc's `ExpSlow.DivHypLG` form -/
theorem ensCLG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpSlow.DivHypLG impl R names 41504 112 (cost DivRec.drsC) :=
  ensRLG impl hap R NatMul.names mul_ns (mul_code impl hap)
    (NatMul.hypXE impl hap R hmk0 hgr hmc hmv0 hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmk0 hmv0 hmz0

end FvModexp.Arm64.NatDiv
