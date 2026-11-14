import FvModexp.Proofs.Amd64.Exp.ModInvL0J
import FvModexp.Proofs.Amd64.Exp.ModInvL1J
import FvModexp.Proofs.Amd64.Exp.ModInvL2J
import FvModexp.Proofs.Amd64.Exp.ModInvL3J
import FvModexp.Proofs.Amd64.Exp.ModInvL4J
import FvModexp.Proofs.Amd64.Exp.ModInvL5J
import FvModexp.Proofs.Amd64.Exp.ModInvF5J

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the Hensel loop (agent infra s58; twin of `Arm64/Exp/ModInvLoop`)

`J2` (the loop head, every round `j`): the round segments compose (`segL0` → `segL1` … `segL5` → `J2` at `j + 1`;
the final round `segF2` … `segF5` → return), and the loop terminates: induction on `numWords - 2^(j-1)` (a round
`j` with `numWords ≤ 2^(j-1)` never reaches the loop head, `J2j` is vacuous there).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

/-- `J2j` holds vacuously for a round that cannot reach the loop head -/
theorem j2_vac {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} {J : Nat}
    (h : 1 ≤ J → 2 ^ (J - 1) < NW n → False) : J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s J := by
  intro S p l c q ql qc L1 b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj1 hjn
  exact (h hj1 hjn).elim

/-- termination: `J2j J` for every round from the round step -/
theorem j2_all {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
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
theorem loop {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfS : ns.contains SubMod2N.fn = false) {kc : Nat} (hkc : SubMod2N.K ≤ kc)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st xp xl xc n : Nat} {s : State}
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm' : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) :
    J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  have hkT' : stkT ≤ kc := by
    have : 4440 ≤ SubMod2N.K := by decide
    omega
  have fin : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204903 (ExF n) (eF n) (kF n) :=
    segF2 hap hns hnf htr hkT' (by omega) hx0 hdf0 (segF3 hap hns hnf hmu hkM hkM1 hmm hx0 hdf0
      (segF4 hap hns hnf htr hkT' (by omega) hx0 hdf0 (segF5a hap hns hnf hls hkL haL hx0 hdf0
        (segF5 hap hns hnfS hkT haT htr hsub hadd hgr hkc hx0 hdf0 hsm'))))
  refine j2_all fun J _ ih => segL0 hap hns hnf hsq hkS hkS1 hsm hsm' hx0 hdf0 J ?_ fin
  exact segL1 hap hns hnf htr hkT' (by omega) hx0 hdf0 J (segL2 hap hns hnf hmu hkM hkM1 hmm hx0 hdf0 J
    (segL3 hap hns hnf htr hkT' (by omega) hx0 hdf0 J (segL4 hap hns hnf hls hkL haL hx0 hdf0 J
      (segL5 hap hns hnfS hkT haT htr hsub hadd hgr hkc hx0 hdf0 ih))))

end FvModexp.Amd64.ModInv
