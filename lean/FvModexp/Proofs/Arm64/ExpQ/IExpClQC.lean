import FvModexp.Proofs.Arm64.ExpQ.IExpClQ
import FvModexp.Proofs.Arm64.NatQ.RemC

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64) on the closed Q-form instances with asm's Q-form division plugged (agent expmc s49)

`ensClQC` = `ensClQ` with `hdQ := Q.NatDiv.ensCLG` (NatQ/DivCG) and `hremQ := Q.NatRem.ensCR` (NatQ/RemC): the only
premises left are the runtime contracts and the budget `hbud : BudClQ` (closed by `ensClBQ` once BudClQ is proved).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.IExp

theorem ensClQC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    {stk above : Nat} (hK : K + 1632 ≤ stk) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above) (hbud : BudClQ) :
    ExpSpecM impl R stk above :=
  ensClQ impl hap R hmk hgr hmc hmv hmz hno hwb hget hput
    (Q.NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz) (Q.NatRem.ensCR impl hap R hgr hmc hwb hmk hmv hmz)
    hKN hk1 hk2 hk3 hstkE hK20 hK h4416 hab hbud

end FvModexp.Arm64.IExp
