import FvModexp.Proofs.Arm64.Exp.LibN
import FvModexp.Proofs.Arm64.Exp.LibNE
import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Arm64.Exp.SlowDefs
import FvModexp.Proofs.Arm64.Nat.LibFree
import FvModexp.Proofs.Arm64.Nat.LibRem
import FvModexp.Proofs.Arm64.Nat.DivDefs
import FvModexp.Proofs.Arm64.Nat.SqrDefs
import FvModexp.Proofs.Arm64.Nat.MulDefs

set_option autoImplicit false

/-! # `IExpCl`'s name-list and code-inclusion facts (agent expmc s41; kept apart for module time) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel (CodeIn)

namespace FvModexp.Arm64.IExp

theorem libN_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibN.program.link impl) := by
  rw [LibN.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libNE_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibNE.program.link impl) := by
  rw [LibNE.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libExp_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibExp.program.link impl) := by
  rw [LibExp.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libFree_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibFree.program.link impl) := by
  rw [LibFree.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

/-- `nat.expNNSlow`'s callees (`sqr`, `mul`, and the `div` premise's functions) -/
def nsSl (nsD : List String) : List String := NatSqr.names ++ NatMul.names ++ nsD

set_option maxHeartbeats 64000000 in
theorem sqr_slow : ∀ x, NatSqr.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide +kernel)
set_option maxHeartbeats 64000000 in
theorem mul_slow : ∀ x, NatMul.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide +kernel)
set_option maxHeartbeats 64000000 in
theorem w_n : ∀ x, LibW.names.contains x = true → LibN.names.contains x = true := MontW.sub_of_all (by decide +kernel)
set_option maxHeartbeats 64000000 in
theorem rem_n : ∀ x, LibRem.names.contains x = true → LibN.names.contains x = true := MontW.sub_of_all (by decide +kernel)
set_option maxHeartbeats 64000000 in
theorem w_11 : LibW.names.contains Extracted.seg11.name = false := by decide +kernel
set_option maxHeartbeats 64000000 in
theorem rem_11 : LibRem.names.contains Extracted.seg11.name = false := by decide +kernel
set_option maxHeartbeats 64000000 in
theorem div_fn : NatDiv.names.contains ExpSlow.fn = false := by decide +kernel
set_option maxHeartbeats 64000000 in
theorem sqr_fn : NatSqr.names.contains ExpSlow.fn = false := by decide +kernel
set_option maxHeartbeats 64000000 in
theorem mul_fn : NatMul.names.contains ExpSlow.fn = false := by decide +kernel

end FvModexp.Arm64.IExp
