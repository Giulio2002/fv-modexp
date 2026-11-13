import FvModexp.Proofs.Amd64.Int.ModFunA
import FvModexp.Proofs.Amd64.NatQ.DivMFull

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64) with `nat.div` discharged: `IMod.ensCA : ModSpecA` (premise: asm's `DivLarge.HypG`)

`IMod.mod_ensD` instantiated with top's `Q.NatDiv.ensML` (`nat.div` as `QuoRem` calls it: `stk == nil`, `z = nil`,
`z2 = u`; program `LibDiv` ⊆ `LibQR` without `QuoRem`, window 41512, above 112). Open premises (until asm's amd64
`divLarge` closes): `Q.DivLarge.HypG impl R dc` and the budget bound of `costMQ dc` within `ModBudget` (the arm64
twin is `IMod.bud`). Runtime premises: the Janus contracts on `Extracted.program.ofImpl impl`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (ModBudget)

theorem libDiv_sub : ∀ x, LibDiv.names.contains x = true → LibQR.names.contains x = true :=
  Callees.sub_of_all (by decide)

theorem libDiv_noQ : LibDiv.names.contains Extracted.seg6.name = false := by decide

/-- **`(*Int).Mod` (amd64)**: `ModSpecA` for any window `stk ≥ 41800` (`nat.div`'s 41512 + `QuoRem`'s 120 + `Mod`'s
168), `above ≥ 16`; premises: the live runtime contracts, `divLarge` (`Q.DivLarge.HypG`) and its cost bound -/
theorem ensCA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput0 : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    (dc : Nat → Nat → Nat) (hL : Q.DivLarge.HypG impl R dc)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → Q.NatDiv.costMQ dc ul vl ≤ ModBudget (max ul vl))
    {stk above : Nat} (hstk : 41800 ≤ stk) (hab : 16 ≤ above) :
    ModSpecA impl R stk above :=
  mod_ensD impl hap R (Q.NatDiv.ensML impl hap R hmk0 hmv0 hmz0 hno0 hget0 hput0 dc hL) libDiv_sub libDiv_noQ
    (WbLiveContract64.of_codeIn (by rw [LibQR.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibQR.names) hwb4)
    (by omega) (by omega) (by decide) hab hbud

end FvModexp.Amd64.IMod
