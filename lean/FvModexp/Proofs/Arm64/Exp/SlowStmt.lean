import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the exported statement shape (agent expmc)

* `ExpSlow.cost sqC mlC dvC ℓ xl yl ml`: `z.set(x)`'s `makeslice` plus `64 · yl` loop bodies (at most `w ≤ 63` top
  iterations and `64 (yl - 1)` lower ones), each bounded by the box maxima of the callee costs over the lengths the
  loop can see: with `M = max (len x) (len m)`, `len z ≤ M` at `sqr`, `≤ 2M` at `mul`, `≤ 3M` at `div` (TIGHT COSTS,
  expmc s42; the boxes were the constants 128/256/384); `stk`'s length is constant `ℓ`.
* `SlowHypA` (now an alias of `NHyp.SlowHyp`, batch "[expmc s40] ANNOUNCE") = the former `NHyp.SlowHyp` with ONE more
  pre conjunct `SlowX R L x xl xc` (= `NHyp.XFacts`) (FINDING part 2 of NOTES-conventions
  "[expmc s37]"): `zz.mul(stk, z, x)` multiplies by the INPUT `x`, and every `nat.mul` premise form needs of its
  operands the capacity facts (`CapIn0`: `xl ≤ xc < 2^40`, the cap range held — Go's `alias` compares cap ends;
  cf. infra's `P2HypC`) and apartness from the threshold globals `gA` (`OpX`). The coordinator decides where they
  come from (`RunIface.ExpSpec`'s `x.abs` has both). Post `CPostR0` = `CPostR` with `NatOF0`: a `nil` result allowed
  (FINDING part 3; `ExpN.Post` already has that disjunct).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- the budget bound of `nat.expNNSlow` (see the module doc) -/
def cost (sqC : Nat → Nat → Nat) (mlC dvC : Nat → Nat → Nat → Nat) (ℓ xl yl ml : Nat) : Nat :=
  makeCost xl + 64 * yl * (Exp.supN (sqC ℓ) (max xl ml) + Exp.supN (fun n => mlC ℓ n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC ℓ n ml) (3 * max xl ml))

/-- = `NHyp.NatOF0` (moved to `NHyp`, batch "[expmc s40] ANNOUNCE") -/
abbrev NatOF0 := @NHyp.NatOF0

/-- = `NHyp.CPostR0` -/
abbrev CPostR0 := @NHyp.CPostR0

/-- = `NHyp.XFacts` (the extra facts of the operand `x`) -/
abbrev SlowX := @NHyp.XFacts

/-- = `NHyp.SlowHyp` (since the batch, `NHyp.SlowHyp` IS the former `SlowHypA` text) -/
abbrev SlowHypA := @NHyp.SlowHyp

end FvModexp.Arm64.ExpSlow
