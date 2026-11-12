import FvModexp.Proofs.Arm64.Top.RunCallees2
import FvModexp.Proofs.Arm64.Top.RunIfaceMono

set_option autoImplicit false

/-! # `Run` (arm64): the `(*Int).Mod` interface name `ModSpecM` (= `RunIface.ModSpec`, which carries `ModX` since the v0.3.1 re-pin) (agent top s21)

divmc s28 ("[divmc s28] REQUEST top", NOTES-conventions): `z.Mod(z, y)` writes the remainder into `z`'s own array, then
`divLarge` / `divRecursiveStep` / `nat.mul` read the threshold globals at `RunIface.gA`; `IntPre`'s `Held` does not put
that array apart from `gA`. `ModX m z` (divmc's `IMod.ModX` body verbatim) is the missing fact; `ModSpecM` is
`ModSpec` with it as the LAST pre conjunct (= divmc's `IMod.ModSpecX` body verbatim, so divmc's proof is one).
Kept in this NEW module instead of editing `RunIface` (REBUILD COST rule); Run discharges `ModX` from `OpDone`'s fresh
array (`InRanges … R.rt`) and `Globals`' `Outside gA 32 R.rt` (RunC2M). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunIface

/-- **`z.Mod(z, y)`** as Run calls it: since the v0.3.1 re-pin `ModSpec` itself carries `ModX` (last pre conjunct);
`ModSpecM` is kept as its name (abbreviation) so existing users stay valid -/
abbrev ModSpecM (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop := ModSpec impl R stk above

theorem ModSpecM.of_modSpec {impl : List Segment} {R : RtInv} {k a : Nat} (h : ModSpec impl R k a) :
    ModSpecM impl R k a := h

theorem ModSpecM.mono {impl : List Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpecM impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ModSpecM impl R k' a' := ModSpec.mono h hk ha

end FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.RunCallees

set_option linter.defProp false in
/-- `z.Mod(z, y)` (final interface `ModSpecM`) as a callee of `Run`. -/
def modSumM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stk above : Nat)
    (hM : RunIface.ModSpecM impl R stk above) :=
  fun (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) =>
    (libRun_eq ▸ Ensures.toSummaryIn (hM b L z y) (noExit_restrict hap _) (codeIn_restrict_full hap _) :
      Summary (LibRun.program.link impl) _ _ _)

end FvModexp.Arm64.RunCallees
