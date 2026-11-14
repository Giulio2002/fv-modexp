import FvModexp.Proofs.Arm64.Exp.IExpClE
import FvModexp.Proofs.Arm64.Exp.NFunNE
import FvModexp.Proofs.Arm64.Exp.EvCost

set_option autoImplicit false

/-!
# The closed stack-need facts of `(*Int).exp`'s `nat.expNN` (arm64): `IExp.needSE`, `IExp.need_bounds`

The callee shapes (`IExp.dhypsQ`, `slowClQ`, `p2Cl`, cost instances, `rem_mono`/`slow_mono`/`p2_mono`) moved verbatim to
Exp/IExpClE (infra s60) so that arm64 EvenRow does not reach `Exp/NFunNE`; this module re-exports them (import) and keeps
the two declarations that need `ExpN.addN` (NFunNE) / `ExpEven.needE` (EvCost). Names unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.IExp

/-- the slow / even need and cost functions of the closed `(*Int).exp` -/
abbrev needSE : Nat → Nat → Nat → Nat :=
  ExpN.addN ExpSlow.need (ExpEven.needE NatRem.need ExpSlow.need P2D.needP)

/-- the stack-need bound of `IExp.ens` (`hneed`) for the closed needs -/
theorem need_bounds : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    NatRem.need xl n ≤ 2 ^ 16 ∧ needSE xl yl n ≤ 2 ^ 16 ∧ P2D.needP xl yl lm ≤ 2 ^ 16 := by
  intro xl yl n lm hx _ _ hn _
  refine ⟨by simp only [NatRem.need]; omega, ?_, by simp only [P2D.needP]; omega⟩
  simp only [needSE, ExpN.addN, ExpEven.needE, ExpSlow.need, NatRem.need, P2D.needP, StackNat.rnd,
    if_pos (And.intro hx hn)]
  omega

end FvModexp.Arm64.IExp
