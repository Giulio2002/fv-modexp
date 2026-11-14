import FvModexp.Proofs.Amd64.Exp.P2PreRet

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the main loop's induction (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreLoop`)

`head_all_of`: from one round (`HeadJ (i + 2) → HeadJ i` for every even `2 ≤ i ≤ len - 2`) and the exit (`headRet`),
`HeadJ i` for every even `2 ≤ i ≤ len` (strong induction on `len - i`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

theorem head_all_of {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State} (hkc : 4608 ≤ kc) (hpl2 : pl % 2 = 0)
    (hround : ∀ i, i % 2 = 0 → 2 ≤ i → i + 2 ≤ pl → HeadJ impl R kc b L st pw pl ws lm x xl s (i + 2) →
      HeadJ impl R kc b L st pw pl ws lm x xl s i) :
    ∀ n i, pl - i = n → i % 2 = 0 → 2 ≤ i → i ≤ pl → HeadJ impl R kc b L st pw pl ws lm x xl s i := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi2 hi hip
    rcases Nat.eq_or_lt_of_le hip with rfl | hlt
    · exact headRet hkc
    · have hip2 : i + 2 ≤ pl := by omega
      exact hround i hi2 hi hip2 (ih (pl - (i + 2)) (by omega) (i + 2) rfl (by omega) (by omega) hip2)

end FvModexp.Amd64.P2Pre
