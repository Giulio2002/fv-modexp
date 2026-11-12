import FvModexp.Proofs.Amd64.Top.RunDRel

/-!
# `Run` (amd64): the operand phase boundaries

Operand `j` (0 base, 1 exp, 2 mod) runs from `pcD j` (its `big.Int` zeroed) through `getData` (direct slice, or a zeroed
32-byte stack buffer, or `makeslice` + `memmove`) to the `setBytes` call `pcE j`, whose arguments are
`z = (AX, BX, CX) = nil` and `buf = (DI, SI, R8)`; from there one generic segment (`dE`, generated per operand) calls the
patched `nat.setBytes`, stores the result into the `big.Int` and zeroes the next one: `pcD (j + 1)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

abbrev pcD0 : Nat := segAddr Extracted.program fn + 0x60e
abbrev pcD1 : Nat := segAddr Extracted.program fn + 0x762
abbrev pcD2 : Nat := segAddr Extracted.program fn + 0x8f6
abbrev pcD3 : Nat := segAddr Extracted.program fn + 0xa3b
abbrev pcE0 : Nat := segAddr Extracted.program fn + 0x720
abbrev pcE1 : Nat := segAddr Extracted.program fn + 0x8b4
abbrev pcE2 : Nat := segAddr Extracted.program fn + 0xa16

/-- The budget spent at the `D` boundary after `k` operands, and at operand `j`'s `setBytes` call. -/
@[reducible] def cstD (k : Nat) : Nat := 3 * makeCost 4 + k * dCost
@[reducible] def cstE (j : Nat) : Nat := 3 * makeCost 4 + j * dCost + allocCost 1024

/-- The `setBytes` buffer `[bp, bp + bl)` of operand `j` at the call (memory `m`): its big-endian value is the operand,
readable, held, outside the callee's window and below the operand `big.Int`s' slots of the caller. -/
def BufOK (R : RtInv) (Lk : List (Nat × Nat)) (s : State) (m : Janus.Arm64.Memory) (p len : BitVec 64) (j bp bl : Nat) :
    Prop :=
  bl = opLen s p len j ∧ beVal m bp bl = opV s p len j ∧ s.mem.accessible bp bl false = true ∧ bp + bl ≤ 2 ^ 48 ∧
    Held R Lk bp bl ∧ Outside bp bl [((s.regs 4).toNat - 616 - 4160, (s.regs 4).toNat - 616 + 48)]

set_option maxRecDepth 20000 in
/-- The return sites of the three operand `setBytes` calls (go-bigmodexpfix). -/
theorem raSB (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (h : ret = 0x654a65 ∨ ret = 0x654bf9 ∨ ret = 0x654d5b) :
    RetAddr ((Extracted.program.onlySegments [SetBytes.fn]).link impl) ret := by
  rcases h with rfl | rfl | rfl
  · exact raRun impl hap _ (by decide) 0x725 (by decide +kernel) (by decide)
  · exact raRun impl hap _ (by decide) 0x8b9 (by decide +kernel) (by decide)
  · exact raRun impl hap _ (by decide) 0xa1b (by decide +kernel) (by decide)

end FvModexp.Amd64.Run
