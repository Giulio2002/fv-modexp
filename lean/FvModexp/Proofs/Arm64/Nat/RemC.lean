import FvModexp.Proofs.Arm64.Nat.RemEns
import FvModexp.Proofs.Arm64.Nat.DivC

set_option autoImplicit false

/-!
# `nat.rem` (arm64), closed form: `div` discharged by `NatDiv.ensCL` (every callee discharged)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatRem

/-- **`nat.rem`** (arm64): `NHyp.RemHyp` (+ `0 < st`, `RemHypNA`) with every callee discharged; premises = live runtime
contracts on `Extracted.program.ofImpl impl` -/
theorem ensC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    RemHypNA impl R LibRem.names 41712 112 need (cost (NatDiv.cost DivRec.drsC)) :=
  ens impl hap R hgr hmc hwb (NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0)

/-- **`nat.rem`** (arm64), every callee discharged, as expmc's `NHyp.RemHyp` (which now carries `0 < st`: the same
statement as `RemHypNA`) -/
theorem ensCR (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    NHyp.RemHyp impl R LibRem.names 41712 112 need (cost (NatDiv.cost DivRec.drsC)) :=
  ensC impl hap R hgr hmc hwb hmk0 hmv0 hmz0

end FvModexp.Arm64.NatRem
