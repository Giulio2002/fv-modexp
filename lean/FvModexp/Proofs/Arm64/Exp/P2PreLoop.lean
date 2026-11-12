import FvModexp.Proofs.Arm64.Exp.P2PreH
import FvModexp.Proofs.Arm64.Exp.P2PreA
import FvModexp.Proofs.Arm64.Exp.P2PreB
import FvModexp.Proofs.Arm64.Exp.P2PreC
import FvModexp.Proofs.Arm64.Exp.P2PreD
import FvModexp.Proofs.Arm64.Exp.P2PreRet

/-!
# `buildPrecomputationWindowModPower2` (arm64): the main loop (agent infra)

`head_all`: `HeadJ i` for every even `2 ≤ i ≤ len`, by induction on `len - i`: `i = len` is the return (`headRet`),
otherwise one round `segH (segA (segB (segC (segD (HeadJ (i+2))))))`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

theorem head_all (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS stkM aboveM stkT aboveT : Nat}
    (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) :
    ∀ n i, pl - i = n → i % 2 = 0 → 2 ≤ i → i ≤ pl → HeadJ impl R kc sqC mlC b L st pw pl lm x xl s i := by
  have hpl2 := (pl_facts hpre).2.2
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi2 hi hip
    rcases Nat.eq_or_lt_of_le hip with rfl | hlt
    · exact headRet hkc hpre
    · have hip2 : i + 2 ≤ pl := by omega
      exact segH hap hns hnf hsq hkS haS hsm hkc hpre
        (segA hap hns hnf htr hkT haT hwb hkc hpre
          (segB hap hns hnf hmu hkM haM hmm hwb hkc hpre
            (segC hap hns hnf htr hkT haT hwb hkc hpre
              (segD hwb hkc hpre (ih (pl - (i + 2)) (by omega) (i + 2) rfl (by omega) (by omega) hip2))))) hip2

end

end FvModexp.Arm64.P2Pre
