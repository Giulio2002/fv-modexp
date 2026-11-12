import FvModexp.Proofs.Arm64.Nat.DivC
import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Arm64.Exp.LibW

set_option autoImplicit false

/-!
# `nat.div` (arm64) as the windows' / `expNNOdd`'s / `expNN`'s premise `ExpHyp.DivHypL`

asm's CLOSED `nat.div` (`NatDiv.ensCL` / `ensC`, Arm64/Nat/DivC.lean: only live runtime contracts on
`Extracted.program.ofImpl impl` remain): `hyp` (StackBackL form, what the window / odd / expNN statements take) and
`hypS` (`ExpHyp.DivHyp` form), program `LibDiv.names`, window `41504 / 112`, cost `NatDiv.cost DivRec.drsC`. Plus the
name facts the callers' statements ask of `nsD`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DivInst

/-- the cost function of the closed `nat.div` -/
abbrev divC : Nat → Nat → Nat → Nat := NatDiv.cost DivRec.drsC

/-- `nat.div` (arm64), every callee discharged, `ExpHyp.DivHypL` form -/
theorem hyp (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypL impl R LibDiv.names 41504 112 divC :=
  NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0

/-- the same in the `ExpHyp.DivHyp` form -/
theorem hypS (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHyp impl R LibDiv.names 41504 112 divC :=
  NatDiv.ensC impl hap R hgr hmc hwb hmk0 hmv0 hmz0

set_option maxHeartbeats 64000000 in
theorem ns_sub : ∀ x, LibDiv.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)

theorem ns_w4 : LibDiv.names.contains Extracted.seg34.name = false := by decide

theorem ns_w2 : LibDiv.names.contains Extracted.seg35.name = false := by decide

end FvModexp.Arm64.DivInst
