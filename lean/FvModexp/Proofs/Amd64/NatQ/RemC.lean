import FvModexp.Proofs.Amd64.NatQ.RemEns
import FvModexp.Proofs.Amd64.NatQ.Div

set_option autoImplicit false

/-!
# `nat.rem` (amd64), Q-form, `div` discharged (twin of Arm64/NatQ/RemC.lean; divmc s59)

`Q.NatRem.ensCR : NHyp.RemHypQ … (Q.NatDiv.costQ dc)`: `div` by top's `Q.NatDiv.ensD` (`divLarge` discharged); the
premises are the live runtime contracts on `Extracted.program.ofImpl impl` and asm's `divRecursiveStep` summary
(`DivLarge.DrsHypQ`). `stk.nat(k)` is free in the Q-form, so `rem`'s level-free cost is exactly `div`'s.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

/-- **`nat.rem`** (amd64), `div` discharged (premise `DivLarge.DrsHypQ`), as `NHyp.RemHypQ` -/
theorem ensCR (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : Q.DivLarge.DrsHypQ impl R dc) :
    NHyp.RemHypQ impl R LibRem.names 41720 112 need (Q.NatDiv.costQ dc) :=
  ens impl hap R hgr hmc hwb (Q.NatDiv.ensD impl hap R hgr hmc hwb hmk0 hmv0 hmz0 dc hD)

end FvModexp.Amd64.Q.NatRem
