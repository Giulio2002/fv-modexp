import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the per-body budget bound (agent asm s75; the arm64 `Arm64/ExpQ/SlowLoopUQ.perBQ` verbatim)

One loop body (`sqr`, optional `mul`, `div`) costs at most `perBQ sqC mlC dvC xl ml`: the box maxima of the level-free
callee costs over the lengths the loop sees (`len z ≤ M` at `sqr`, `≤ 2M` at `mul`, `≤ 3M` at `div`,
`M = max (len x) (len m)`). Shared by the upper (expmc) and lower (asm) loops.
-/

namespace FvModexp.Amd64.Q.ExpSlow

/-- the per-body budget bound (box maxima of the level-free callee costs over the lengths the loop can see) -/
@[reducible] def perBQ (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl ml : Nat) : Nat :=
  Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC n ml) (3 * max xl ml)

end FvModexp.Amd64.Q.ExpSlow
