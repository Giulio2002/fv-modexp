import FvModexp.Proofs.Arm64.Top.RunModX
import FvModexp.Proofs.Arm64.Int.ModFun

set_option autoImplicit false

/-! # `Run` (arm64): `RunIface.ModSpecM` from divmc's `IMod.ens` (agent top s21)

divmc's `IMod.ModSpecX` is `RunIface.ModSpecM` (same body), so `(*Int).Mod`'s proof is the final interface; the
`gcWriteBarrier4` contract moves from `Extracted.program.ofImpl impl` to `LibMod` by `CodeIn`. Premise left: `nat.div`
with nil stack and in-place remainder (`IMod.DivHypM`, asm s32) and its cost bound. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Run

theorem modSpecM_ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {nsD : List String} {stkD aboveD : Nat} {costM : Nat → Nat → Nat}
    (hDM : IMod.DivHypM impl R nsD stkD aboveD costM)
    (hnsD : ∀ x, nsD.contains x = true → LibMod.names.contains x = true)
    (hnsQ : nsD.contains Extracted.seg6.name = false) (habD : aboveD ≤ 120)
    (hbudM : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → costM ul vl ≤ RunIface.ModBudget (max ul vl))
    {stkM aboveM : Nat} (hstkD : stkD + 304 ≤ stkM) (h4448 : 4448 ≤ stkM) (hab : 32 ≤ aboveM) :
    RunIface.ModSpecM impl R stkM aboveM :=
  IMod.ens impl hap R hDM hnsD hnsQ
    (WbLiveContract.of_codeIn (by rw [LibMod.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _) hwb4)
    hstkD habD h4448 hab hbudM

end FvModexp.Arm64.Run
