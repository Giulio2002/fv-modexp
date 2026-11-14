import FvModexp.Proofs.Amd64.Exp.NFun
import FvModexp.Proofs.Amd64.Exp.EvNHyp

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): asm's even-path premise `EvenHyp.ExpNNHypNE1` from `ExpN.ens_noEven` (agent expmc s77; twin of
the arm64 `ExpNNHypNE.toNE1`, Arm64/Exp/NCap.lean)

On amd64 `ExpNNHypNE1` (Amd64/Exp/EvNHyp.lean) is stated with `ExpN.Pre` / `ExpN.Post` verbatim (the result's cap bound
and location are already conjuncts of `ExpN.Post`), so it is `ens_noEven` itself: the recursive `expNN` calls of
`nat.expNNEven` (odd part, power-of-two part) are discharged by the stack-given, no-even-path `expNN` summary.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- **`EvenHyp.ExpNNHypNE1`** from `nat.expNN`'s callee shapes -/
theorem hypNE1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388) :
    EvenHyp.ExpNNHypNE1 impl R K costF costD needR costR needS needP costS costP :=
  fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
    ens_noEven impl hap R H hRem hnsR hnfR hKR b L zp zl zc st xp xl xc yp yl yc mp n mc slow

end FvModexp.Amd64.ExpN
