import FvModexp.Proofs.Arm64.Top.RunModI
import FvModexp.Proofs.Arm64.Nat.DivMC
import FvModexp.Proofs.Arm64.Int.ModBud

set_option autoImplicit false

/-!
# `(*Int).Mod` (arm64) as `Run` calls it, every callee proved (agent top s30; moved from the retired `RunOkRowM`)

`modSpecM_C` = `modSpecM_ens` with asm's `NatDiv.ensMC` (`nil.div(nil, u, u, v)`) and divmc's `IMod.bud`.
-/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool Janus.Contracts.EqHashModel
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- `(*Int).Mod` with `nat.div` and the budget discharged (= divmc's `IMod.ensC`, in the `ModSpecM` form) -/
theorem modSpecM_C (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {stkM aboveM : Nat} (hstkD : 41504 + 304 ≤ stkM) (hab : 32 ≤ aboveM) :
    RunIface.ModSpecM impl R stkM aboveM :=
  modSpecM_ens impl hap R hwb4 (NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput)
    NatDiv.libDiv_sub_mod NatDiv.libDiv_noQuoRem (by decide) IMod.bud hstkD (by omega) hab


end FvModexp.Arm64.Run
