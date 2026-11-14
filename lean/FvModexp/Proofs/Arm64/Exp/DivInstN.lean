import FvModexp.Proofs.Arm64.Nat.LibDiv
import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Arm64.Exp.LibW

set_option autoImplicit false

/-!
# `nat.div`'s name facts (arm64) for the Q-form callee shapes (agent expmc s69)

The name facts of `Exp/DivInst.lean` (`ns_sub`/`ns_w4`/`ns_w2`, same proofs) WITHOUT its import of asm's old-cost
`Nat/DivC` (which reaches the retired old `nat.mul` SCC): the Q-form `IExp.dhypsQ` (Exp/IExpClD.lean) uses these.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DivInstN

set_option maxHeartbeats 64000000 in
theorem ns_sub : ∀ x, LibDiv.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)

theorem ns_w4 : LibDiv.names.contains Extracted.seg34.name = false := by decide

theorem ns_w2 : LibDiv.names.contains Extracted.seg35.name = false := by decide

end FvModexp.Arm64.DivInstN
