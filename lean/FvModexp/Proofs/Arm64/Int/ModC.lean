import FvModexp.Proofs.Arm64.Int.ModFun
import FvModexp.Proofs.Arm64.Int.ModBud
import FvModexp.Proofs.Arm64.Nat.DivMC

set_option autoImplicit false

/-!
# `(*Int).Mod` (arm64) with every callee discharged: `IMod.ensC : ModSpecX` (= `RunIface.ModSpec`)

`IMod.ens` instantiated with asm's `NatDiv.ensMC` (`nat.div` as `QuoRem` calls it: `stk == nil`, `z = nil`, `z2 = u`;
program `LibDiv` ⊆ `LibMod` without `QuoRem`, window 41504, above 112) and the budget lemma `IMod.bud`. Premises: the
Janus runtime contracts on `Extracted.program.ofImpl impl` only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
open Janus.Contracts.Pool Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Arm64.IMod

/-- **`(*Int).Mod` (arm64), no open callee premise**: `z.Mod(z, y)` meets `ModSpecX` (= `RunIface.ModSpec`) for any
window `stk ≥ 41808` (`nat.div`'s 41504 + QuoRem/Mod frames) and `above ≥ 32`. -/
theorem ensC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {stk above : Nat} (hstk : 41808 ≤ stk) (hab : 32 ≤ above) :
    ModSpecX impl R stk above :=
  ens impl hap R (NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput)
    NatDiv.libDiv_sub_mod NatDiv.libDiv_noQuoRem
    (WbLiveContract.of_codeIn (by rw [LibMod.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _) hwb4)
    hstk (by decide) (by omega) hab bud

end FvModexp.Arm64.IMod
