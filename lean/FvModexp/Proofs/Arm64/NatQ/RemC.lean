import FvModexp.Proofs.Arm64.NatQ.RemEns
import FvModexp.Proofs.Arm64.NatQ.DivCG

set_option autoImplicit false

/-!
# `nat.rem` (arm64), closed, Q-form (TIGHT COSTS, asm s39): `Q.NatRem.ensCR : NHyp.RemHypQ … (Q.NatDiv.costQ drsCQ)`

Q twin of Arm64/Nat/RemC.lean: `div` discharged by `Q.NatDiv.ensCL` (every callee discharged); the premises are the
live runtime contracts on `Extracted.program.ofImpl impl`. `stk.nat(k)` is free in the Q-form, so `rem`'s level-free
cost is exactly `div`'s.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem

/-- **`nat.rem`** (arm64), every callee discharged, as expmc's `NHyp.RemHypQ` (Q-form of `NHyp.RemHyp`) -/
theorem ensCR (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    NHyp.RemHypQ impl R LibRem.names 41712 112 need (Q.NatDiv.costQ Q.drsCQ) :=
  ens impl hap R hgr hmc hwb (Q.NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0)

end FvModexp.Arm64.Q.NatRem
