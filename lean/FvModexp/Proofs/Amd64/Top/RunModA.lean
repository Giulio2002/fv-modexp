import FvModexp.Proofs.Amd64.Int.ModCA
import FvModexp.Proofs.Amd64.NatQ.DivMC
import FvModexp.Proofs.Amd64.NatQ.ModBudQ
import FvModexp.Proofs.Amd64.Top.RunIfaceA

set_option autoImplicit false

/-! # `Run` (amd64): `(*Int).Mod` closed, as Run calls it (`RunIface.ModSpecA`, window 41800 / 16) (agent top s49)

divmc's `IMod.mod_ensD` with asm's closed `Q.NatDiv.ensMC` (`nat.div` as `QuoRem` calls it) and the closed budget
`Q.BudM.bud` (as amd64 `ModRow.correctness`); premises: the Janus runtime contracts on `Extracted.program.ofImpl impl`.
`IMod.ModSpecA` is `RunIface.ModSpecA` (the light copy Run's segments use) by definition. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Run.Closed

theorem modA_eq (impl : List Amd64.Segment) (R : RtInv) (k a : Nat) :
    IMod.ModSpecA impl R k a = RunIface.ModSpecA impl R k a := rfl

set_option maxHeartbeats 64000000 in
/-- **`(*Int).Mod`** (amd64) as `Run` calls it, every machine-code callee proved -/
theorem modA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4) :
    RunIface.ModSpecA impl R 41800 16 :=
  IMod.mod_ensD impl hap R (Q.NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput) IMod.libDiv_sub
    IMod.libDiv_noQ
    (WbLiveContract64.of_codeIn (by rw [LibQR.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibQR.names) hwb4)
    (stk := 41800) (above := 16) (by omega) (by omega) (by decide) (by decide) Q.BudM.bud

end FvModexp.Amd64.Run.Closed
