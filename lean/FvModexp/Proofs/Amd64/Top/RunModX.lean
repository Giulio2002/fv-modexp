import FvModexp.Proofs.Amd64.Top.RunIfaceMono

set_option autoImplicit false

/-! # `Run` (amd64): the `(*Int).Mod` interface name `ModSpecM` (= `RunIface.ModSpec`, which carries `ModX` since the v0.3.1 re-pin) (agent top s21)

Twin of the arm64 `Top/RunModX` (divmc s28 request): `ModX m z` = `z`'s array (when it has one) apart from the threshold
globals at `RunIface.gA`; `ModSpecM` = `ModSpec` with it as the LAST pre conjunct. NEW module instead of a `RunIface` edit
(REBUILD COST rule). Run discharges `ModX` in RunC2M (OpDone's fresh array, `Globals`' `Outside gA 32 R.rt`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RunIface

/-- **`z.Mod(z, y)`** as Run calls it: since the v0.3.1 re-pin `ModSpec` itself carries `ModX` (last pre conjunct);
`ModSpecM` is kept as its name (abbreviation) so existing users stay valid -/
abbrev ModSpecM (impl : List Janus.Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop := ModSpec impl R stk above

theorem ModSpecM.of_modSpec {impl : List Janus.Amd64.Segment} {R : RtInv} {k a : Nat} (h : ModSpec impl R k a) :
    ModSpecM impl R k a := h

theorem ModSpecM.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpecM impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ModSpecM impl R k' a' := ModSpec.mono h hk ha

end FvModexp.Amd64.RunIface
