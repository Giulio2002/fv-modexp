import FvModexp.Proofs.Amd64.NatQ.DrsStep
import FvModexp.Proofs.Amd64.NatQ.NatMul
import FvModexp.Proofs.Amd64.Nat.RowLink

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsRowWQ.lean, part 1)
# Row support for `nat.divRecursiveStep` (amd64): the `nat.mul` premise's program side conditions

`mul_ns` (`nat.mul`'s program leaves out `divRecursiveStep`, NESTED-PROGRAM RULE) and `mul_code` (it sits inside `LibDrs`),
so that `Q.DivRec.hyp` can take divmc's `Q.NatMul.hypQE` for its `nat.mul` calls. The witness part (initial state,
`setup`, `preQ`) follows (asm s55).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DrsRowQ

theorem mul_ns : Q.NatMul.names.contains DivLarge.drsFn = false := by decide

theorem mul_code (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 ((Extracted.program.onlySegments Q.NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide))

end FvModexp.Amd64.DrsRowQ
