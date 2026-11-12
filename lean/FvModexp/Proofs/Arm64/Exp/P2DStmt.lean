import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the callee shape `P2HypC` (agent infra, s39)

`NHyp.P2Hyp` plus the pre conjunct `len x ≤ cap x < 2^40` (NOTES-conventions "[infra s39] FINDING"): the even-base path
runs `nat(nil).rsh(x, i)`, whose `x[m-n:]` slice keeps the pointer offset only when `cap x − (m − n) ≠ 0`; with an
unconstrained `cap x` register the statement is false. Since expmc's batched edit (s41) `NHyp.P2Hyp` has this text; `P2HypC` is an alias.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NHyp2

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

/-- = `NHyp.P2Hyp` (since expmc's batch "[expmc s40] ANNOUNCE", `NHyp.P2Hyp` IS this text: the former `P2Hyp` pre
`∧ xl ≤ xc ∧ xc < 2^40`) -/
abbrev P2HypC := @NHyp.P2Hyp

end FvModexp.Arm64.NHyp2
