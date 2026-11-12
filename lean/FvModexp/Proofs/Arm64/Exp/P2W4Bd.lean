import FvModexp.Proofs.Arm64.Exp.P2W4B0
import FvModexp.Proofs.Arm64.Exp.P2W4B1
import FvModexp.Proofs.Arm64.Exp.P2W4B2
import FvModexp.Proofs.Arm64.Exp.P2W4B3
import FvModexp.Proofs.Arm64.Exp.P2W4B4
import FvModexp.Proofs.Arm64.Exp.P2W4B5
import FvModexp.Proofs.Arm64.Exp.P2W4B6
import FvModexp.Proofs.Arm64.Exp.P2W4B7
import FvModexp.Proofs.Arm64.Exp.P2W4B8
import FvModexp.Proofs.Arm64.Exp.P2W4B9
import FvModexp.Proofs.Arm64.Exp.P2W4B10

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the loop body premise of `loopKL` (agent infra)

`bodyKI : KI i c → KI i (c + 1)` = `B0 ∘ B1 ∘ … ∘ B10` (nat.go:1069-1105).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

/-- **the loop body** (premise `hbody` of `loopKL`) -/
theorem bodyKI (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ K) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1) (hcb : cst ≤ b)
    (i c : Nat) (KN : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c) :
    KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i (c + 1) := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  exact segB0 hap hns hnf hsq hkS haS hsm hP hcb
    (segB1 hap hns hnf htr hkT haT hP
      (segB2 hap hns hnf hsq hkS haS hsm hP
        (segB3 hap hns hnf htr hkT haT hP
          (segB4 hap hns hnf hsq hkS haS hsm hP
            (segB5 hap hns hnf htr hkT haT hP
              (segB6 hap hns hnf hsq hkS haS hsm hP
                (segB7 hap hns hnf htr hkT haT hP
                  (segB8 hap hns hnf hmu hkM haM hmm hP hX
                    (segB9 hap hns hnf htr hkT haT hP (segB10 hP KN))))))))))
    S M L1 b1 pA lA cA pB lB cB h

end

end FvModexp.Arm64.P2W4
