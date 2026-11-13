import FvModexp.Proofs.Arm64.Exp.ModInvL0
import FvModexp.Proofs.Arm64.Exp.ModInvL1
import FvModexp.Proofs.Arm64.Exp.ModInvL2
import FvModexp.Proofs.Arm64.Exp.ModInvL3
import FvModexp.Proofs.Arm64.Exp.ModInvL4
import FvModexp.Proofs.Arm64.Exp.ModInvL5
import FvModexp.Proofs.Arm64.Exp.ModInvF1
import FvModexp.Proofs.Arm64.Exp.ModInvF2
import FvModexp.Proofs.Arm64.Exp.ModInvF3
import FvModexp.Proofs.Arm64.Exp.ModInvF4
import FvModexp.Proofs.Arm64.Exp.ModInvF5

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the Hensel loop (agent infra)

`J2` (the loop head, every round `j`): the round segments compose (`segL0` → `segL1` … `segL5` → `J2` at `j + 1`;
the final round `segF1` … `segF5` → return), and the loop terminates: induction on `numWords - 2^(j-1)` (a round
`j` with `numWords ≤ 2^(j-1)` never reaches the loop head, `J2j` is vacuous there).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- `J2j` holds vacuously for a round that cannot reach the loop head -/
theorem j2_vac {impl : List Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} {J : Nat}
    (h : 1 ≤ J → 2 ^ (J - 1) < NW n → False) : J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s J := by
  intro S p l c q ql qc L1 b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj1 hjn
  exact (h hj1 hjn).elim

/-- termination: `J2j J` for every round from the round step -/
theorem j2_all {impl : List Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (step : ∀ J, 1 ≤ J → J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s (J + 1) →
      J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s J) :
    J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  have key : ∀ m J, NW n - 2 ^ (J - 1) ≤ m → J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s J := by
    intro m
    induction m with
    | zero => intro J h; exact j2_vac fun _ h' => by omega
    | succ m ih =>
      intro J h
      rcases Nat.eq_zero_or_pos J with rfl | hJ
      · exact j2_vac fun h1 _ => by omega
      · by_cases hc : NW n ≤ 2 ^ (J - 1)
        · exact j2_vac fun _ h' => by omega
        · refine step J hJ (ih (J + 1) ?_)
          have e : 2 ^ (J + 1 - 1) = 2 ^ (J - 1) * 2 := by
            rw [show J + 1 - 1 = (J - 1) + 1 by omega, Nat.pow_succ]
          have := Nat.one_le_two_pow (n := J - 1)
          rw [e]; omega
  exact fun J => key _ J (Nat.le_refl _)

set_option maxRecDepth 20000 in
/-- **the loop**: `J2` at every round, from the callees' summaries -/
theorem loop {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false) {kc : Nat} (hkc : 4608 ≤ kc)
    {H : Nat} {sqrC : Nat → Nat} {stkS aboveS : Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mulC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mulC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat}
    {s : State} (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c') :
    J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  have fin : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1798112 (ExF n) (eF n) (kF n) :=
    segF1 hap hns hnf htr hkc hkT haT (segF2 hap hns hnf hmu hkc hkM haM hmm
      (segF3 hap hns hnf htr hkc hkT haT (segF4 hap hns hnf hls hkc hkL haL
        (segF5 hap hns hnfS hkT4 haT htr hsub hadd hgr hkc hsm))))
  refine j2_all fun J _ ih => segL0 hap hns hnf hsq hkc hkS haS hsm J ?_ fin
  exact segL1 hap hns hnf htr hkc hkT haT (segL2 hap hns hnf hmu hkc hkM haM hmm
    (segL3 hap hns hnf htr hkc hkT haT (segL4 hap hns hnf hls hkc hkL haL
      (segL5 hap hns hnfS hkT4 haT htr hsub hadd hgr hkc ih))))

end FvModexp.Arm64.ModInv
