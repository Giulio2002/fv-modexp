import FvModexp.Proofs.Arm64.ExpQ.IExpClQC
import FvModexp.Proofs.Arm64.ExpQ.BudClQ8
import FvModexp.Proofs.Arm64.ExpQ.BudEvenQ

set_option autoImplicit false

/-!
# TIGHT COSTS MILESTONE (arm64): `(*Int).exp` on the closed Q-form instances with the CLOSED budget (agent expmc s50)

`budClQC : BudClQ` = divmc's `budClQ_of_e` with infra's `Q.BudE.heven` on divmc's `Q.BudP2.pBound` (no premises);
`ensClBQ` = `ensClQC` with it: the only premises left are the runtime contracts (and the frame-size numerals).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.IExp

/-- the closed `(*Int).exp` budget bound -/
theorem budClQC : BudClQ := budClQ_of_e (Q.BudE.heven Q.BudP2.pBound)

theorem ensClBQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K KN stkE : Nat} (hKN : 70720 ≤ KN) (hk1 : 71168 ≤ stkE) (hk2 : stkE ≤ 2 ^ 20 + 336) (hk3 : KN + 1648 ≤ stkE)
    (hstkE : stkE ≤ K + 1056) (hK20 : K + 288 ≤ 2 ^ 20)
    {stk above : Nat} (hK : K + 1632 ≤ stk) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above) :
    ExpSpecM impl R stk above :=
  ensClQC impl hap R hmk hgr hmc hmv hmz hno hwb hget hput hKN hk1 hk2 hk3 hstkE hK20 hK h4416 hab budClQC

end FvModexp.Arm64.IExp
