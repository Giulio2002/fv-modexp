import FvModexp.Proofs.Amd64.Exp.P2W4B0
import FvModexp.Proofs.Amd64.Exp.P2W4BGT
import FvModexp.Proofs.Amd64.Exp.P2W4BGS
import FvModexp.Proofs.Amd64.Exp.P2W4B8
import FvModexp.Proofs.Amd64.Exp.P2W4B10

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the loop body premise of `loopKL` (agent divmc s77; amd64 twin of agent
infra's `Arm64.P2W4Bd`)

`bodyKI : KI i c → KI i (c + 1)` = `B0 ∘ T ∘ S ∘ T ∘ S ∘ T ∘ S ∘ T ∘ B8 ∘ T ∘ B10` (nat.go:1069-1104): the generic
trunc (`segT`, join pcs +0x686/+0x6dc/+0x732/+0x788/+0x814) and sqr (`segS`, +0x69c/+0x6f2/+0x748) segments.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

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
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  have k10 : KJ impl ret0 Q (J10 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segB10 hP KN
  have k9 : KJ impl ret0 Q (J9 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segT hap hns hnf htr hkT haT hP (jp := 0x814) (by omega) (by cases u <;> rfl) (by omega) (by omega) k10
  have k8 : KJ impl ret0 Q (J8 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segB8 hap hns hnf hml hkM hkM1 hP hX hadx k9
  have k7 : KJ impl ret0 Q (J7 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segT hap hns hnf htr hkT haT hP (jp := 0x788) (by omega) (by cases u <;> rfl) (by omega) (by omega) k8
  have k6 : KJ impl ret0 Q (J6 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segS hap hns hnf hsq hkS hkS1 hP hadx (jp := 0x748) (by cases u <;> rfl) (by omega) (by omega) k7
  have k5 : KJ impl ret0 Q (J5 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segT hap hns hnf htr hkT haT hP (jp := 0x732) (by omega) (by cases u <;> rfl) (by omega) (by omega) k6
  have k4 : KJ impl ret0 Q (J4 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segS hap hns hnf hsq hkS hkS1 hP hadx (jp := 0x6f2) (by cases u <;> rfl) (by omega) (by omega) k5
  have k3 : KJ impl ret0 Q (J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segT hap hns hnf htr hkT haT hP (jp := 0x6dc) (by omega) (by cases u <;> rfl) (by omega) (by omega) k4
  have k2 : KJ impl ret0 Q (J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segS hap hns hnf hsq hkS hkS1 hP hadx (jp := 0x69c) (by cases u <;> rfl) (by omega) (by omega) k3
  have k1 : KJ impl ret0 Q (J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) :=
    segT hap hns hnf htr hkT haT hP (jp := 0x686) (by omega) (by cases u <;> rfl) (by omega) (by omega) k2
  exact segB0 hap hns hnf hsq hkS hkS1 hP hadx hcb k1 S M L1 b1 pA lA cA pB lB cB h

end

end FvModexp.Amd64.P2W4
