import FvModexp.Proofs.Amd64.Exp.P2W2B0
import FvModexp.Proofs.Amd64.Exp.P2W2B1
import FvModexp.Proofs.Amd64.Exp.P2W2B2
import FvModexp.Proofs.Amd64.Exp.P2W2B3
import FvModexp.Proofs.Amd64.Exp.P2W2B4
import FvModexp.Proofs.Amd64.Exp.P2W2B5
import FvModexp.Proofs.Amd64.Exp.P2W2B6

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop body premise of `loopKL` (agent divmc s73; amd64 twin of agent
infra's `Arm64.P2W2Bd`)

`bodyKI : KI i c → KI i (c + 1)` = `B0 ∘ B1 ∘ … ∘ B6` (nat.go:1223-1247).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

/-- **the loop body** (premise `hbody` of `loopKL`) -/
theorem bodyKI (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    {kM : Nat} (hml : FvModexp.Amd64.Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ K) (hkM1 : mulWX64 ≤ kM)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) (hcb : cst ≤ b)
    (i c : Nat) (KN : KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c) :
    KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i (c + 1) := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  exact segB0 hap hns hnf hsq hkS hkS1 hP hadx hcb
    (segB1 hap hns hnf htr hkT haT hP
      (segB2 hap hns hnf hsq hkS hkS1 hP hadx
        (segB3 hap hns hnf htr hkT haT hP
          (segB4 hap hns hnf hml hkM hkM1 hP hX hadx
            (segB5 hap hns hnf htr hkT haT hP (segB6 hP KN))))))
    S M L1 b1 pA lA cA pB lB cB h

end

end FvModexp.Amd64.P2W2
