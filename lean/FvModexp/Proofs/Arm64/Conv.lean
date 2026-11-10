import Extracted
import FvModexp.Proofs.Common.Conv

/-!
# Conventions for function summaries (arm64)

See `docs/CONVENTIONS.md`. `CallEnv` is the part of every precondition that talks about the Go call
environment (stack, goroutine, read-only data, runtime-owned memory); the numbers `stk` (bytes below `SP`
the call may use: its own frame, the deeper frames, the 4096 bytes of every runtime call) and `above`
(bytes of the caller's argument/spill area above `SP` the function writes) are per function.
-/

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The stack window of a summary: `[SP - stk, SP + above)`. -/
@[reducible] def win (s : State) (stk above : Nat) : List (Nat × Nat) := [(s.sp.toNat - stk, s.sp.toNat + above)]

/-- The call environment of a summary of a function that needs `stk` bytes of stack below `SP` and
writes `above` bytes above it:
* the stack-growth prologue of every frame falls through (`GuardOK s stk`), `SP` aligned, the window writable;
* the extracted read-only data is loaded;
* the window is outside the runtime-owned ranges, the goroutine's `stackguard0` slot is outside both;
* no live object lies in the window. -/
def CallEnv (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  GuardOK s stk ∧ StackOK s stk above ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - stk) (stk + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above)

/-- The program of a function proof: the code of the functions `names` plus the runtime stand-in. -/
@[reducible] def prog (names : List String) (impl : List Segment) : Program :=
  (Extracted.program.onlySegments names).link impl

/-- The address of a runtime contract of the extraction. -/
@[reducible] def cA (name : String) : Nat := Extracted.program.contractAddr name

end FvModexp.Arm64
