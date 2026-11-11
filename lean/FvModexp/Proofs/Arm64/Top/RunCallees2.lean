import FvModexp.Proofs.Arm64.Top.LibRun
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.Link

/-! # `Run` (arm64): the Int-level callees (`(*Int).Mod`, `(*Int).exp`, `(*Int).Bytes`) as summaries on `LibRun.program`

`LibRun.program` holds every segment of the Run extraction (it is `Extracted.program`), so each callee's `Ensures` on its
own restricted program moves to it by `codeIn_restrict_full`. The specs (`RunIface.ModSpec`, …) are premises of the
compute part; their proofs (agents divmc / expmc / top) discharge them in the row theorem. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunCallees

/-- The library program of `Run` is the whole extraction. -/
theorem libRun_eq : LibRun.program = Extracted.program := rfl

set_option linter.defProp false in
/-- `z.Mod(z, y)` as a callee of `Run`. -/
def modSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stk above : Nat)
    (hM : RunIface.ModSpec impl R stk above) :=
  fun (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) =>
    (libRun_eq ▸ Ensures.toSummaryIn (hM b L z y) (noExit_restrict hap _) (codeIn_restrict_full hap _) :
      Summary (LibRun.program.link impl) _ _ _)

set_option linter.defProp false in
/-- `z.exp(z, y, m, false)` as a callee of `Run`. -/
def expSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stk above : Nat)
    (hE : RunIface.ExpSpec impl R stk above) :=
  fun (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64) =>
    (libRun_eq ▸ Ensures.toSummaryIn (hE b L z y mm) (noExit_restrict hap _) (codeIn_restrict_full hap _) :
      Summary (LibRun.program.link impl) _ _ _)

set_option linter.defProp false in
/-- `x.Bytes()` as a callee of `Run`. -/
def bytesSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stk above : Nat)
    (hB : RunIface.BytesSpec impl R stk above) :=
  fun (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) =>
    (libRun_eq ▸ Ensures.toSummaryIn (hB b L x) (noExit_restrict hap _) (codeIn_restrict_full hap _) :
      Summary (LibRun.program.link impl) _ _ _)

end FvModexp.Arm64.RunCallees
