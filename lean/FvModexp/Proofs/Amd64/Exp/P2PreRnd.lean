import FvModexp.Proofs.Amd64.Exp.P2PreH
import FvModexp.Proofs.Amd64.Exp.P2PreA
import FvModexp.Proofs.Amd64.Exp.P2PreB
import FvModexp.Proofs.Amd64.Exp.P2PreC
import FvModexp.Proofs.Amd64.Exp.P2PreD
import FvModexp.Proofs.Amd64.Exp.P2PreLoop

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): one main-loop round and the whole loop (agent divmc s65; twin of infra's
`Arm64/Exp/P2PreLoop`)

`round`: `HeadJ (i + 2) → HeadJ i` (`segH ∘ segA ∘ segB ∘ segC ∘ segD`); `head_all`: `HeadJ 2` (`head_all_of`).
Callee premises: `SqrE` (window `kS ≥ sqrW 128`), `Q.DivRec.MulHypQE` (window `kM ≥ mulWX64`), `Trunc.Hyp2`, the live
`gcWriteBarrier2` contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

theorem round (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc) :
    ∀ i, i % 2 = 0 → 2 ≤ i → i + 2 ≤ pl → HeadJ impl R kc b L st pw pl ws lm x xl s (i + 2) →
      HeadJ impl R kc b L st pw pl ws lm x xl s i := fun _ _ _ hip kH =>
  segH hap hns hnf hsq hkS1 hkS hkc (segA hap hns hnf htr hkT haT hwb hkc (segB hap hns hnf hml hkM1 hkM hwb hkc
    (segC hap hns hnf htr hkT haT hwb hkc (segD hwb hkc kH)))) hip

theorem head_all (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpl2 : pl % 2 = 0) (hpl : 2 ≤ pl) : HeadJ impl R kc b L st pw pl ws lm x xl s 2 :=
  head_all_of hkc hpl2 (round hap hns hnf hsq hkS1 hkS hml hkM1 hkM htr hkT haT hwb hkc) (pl - 2) 2 rfl (by decide)
    (Nat.le_refl _) hpl

end

end FvModexp.Amd64.P2Pre
