import Extracted
import FvModexp.Proofs.Common.Conv

/-!
# Conventions for function summaries (amd64)

See `docs/CONVENTIONS.md`. As `FvModexp.Arm64.CallEnv`, for the amd64 Go ABIInternal: `RSP = s.regs 4`, `g = R14`.
The window `[RSP - stk, RSP + above)` includes the return-address slot `[RSP, RSP + 8)` (take `above ≥ 8`).
-/

namespace FvModexp.Amd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

/-- The stack window of a summary: `[RSP - stk, RSP + above)`. -/
@[reducible] def win (s : State) (stk above : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - stk, (s.regs 4).toNat + above)]

/-- The call environment of a summary (amd64): the stack-growth prologues fall through, `RSP` 8-aligned, the window
writable, the read-only data loaded, the window and the `stackguard0` slot outside the runtime-owned ranges and apart,
no live object in the window. -/
def CallEnv (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  StackGuardOK s stk ∧ StackWritable s stk above ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - stk) (stk + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above)

/-- The address of a runtime contract of the extraction. -/
@[reducible] def cA (name : String) : Nat := Extracted.program.contractAddr name

end FvModexp.Amd64
