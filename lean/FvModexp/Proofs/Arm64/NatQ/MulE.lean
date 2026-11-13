import FvModexp.Proofs.Arm64.NatQ.MulHypQ
import FvModexp.Proofs.Arm64.NatQ.MulHypQE

set_option autoImplicit false

/-!
# divmc's exact-write Q `nat.mul` premise is asm's `Q.DivRec.MulHypQE` (TIGHT COSTS, asm s39)

`EvenHyp.MulHypQE` (divmc, NatQ/MulHypQ.lean, proved by `Q.NatMul.hypQE`) and `Q.DivRec.MulHypQE` (asm, the premise of
`Q.DivRec.hyp`) have the same text up to the exact-write clause's name (`EvenHyp.ExactE` / `Q.DivRec.ExactR`, both
`@[reducible]` with the same body), so the bridge is the identity.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.NatDiv

theorem mulE {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat} {cost : Nat → Nat → Nat}
    (h : EvenHyp.MulHypQE impl R ns stk above cost) : Q.DivRec.MulHypQE impl R ns stk above cost := h

end FvModexp.Arm64.Q.NatDiv
