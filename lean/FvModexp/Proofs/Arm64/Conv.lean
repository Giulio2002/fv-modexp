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

/-- The two parts of the window a summary may change (arm64): the window without the caller's saved frame pointer
`[SP - 8, SP)` and saved link register `[SP, SP + 8)`, which the caller reloads after the call (NOTES-divmc issue 2). Every
postcondition's `MemFrame` uses `winA`, never `win`. -/
@[reducible] def winA (s : State) (stk above : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - stk, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + above)]

/-- The extraction's read-only data lies outside the runtime-owned ranges (so that `DataLoaded` survives a call:
`FvModexp.dataLoaded_frame`). -/
def RoOut (R : RtInv) : Prop := ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt

/-- The call environment of a summary of a function that needs `stk` bytes of stack below `SP` and
writes `above` bytes above it:
* the stack-growth prologue of every frame falls through (`GuardOK s stk`), `SP` aligned, the window writable;
* the extracted read-only data is loaded;
* the window is outside the runtime-owned ranges, the goroutine's `stackguard0` slot is outside both;
* no live object lies in the window;
* the read-only data lies outside the runtime-owned ranges. -/
def CallEnv (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  GuardOK s stk ∧ StackOK s stk above ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - stk) (stk + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above) ∧ RoOut R

/-- The program of a function proof: the code of the functions `names` plus the runtime stand-in. -/
@[reducible] def prog (names : List String) (impl : List Segment) : Program :=
  (Extracted.program.onlySegments names).link impl

/-- The address of a runtime contract of the extraction. -/
@[reducible] def cA (name : String) : Nat := Extracted.program.contractAddr name

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec

/-- A read-only data object (`x`, `l` inside data object `k`) is apart from every writable range: one `Apart`
fact instead of `janus_data hd [hw]`'s one disjunction per data object (49 of them, which make `omega` slow). -/
theorem apart_of_data {m : Memory} (hd : Extracted.program.DataLoaded m) (k : Nat)
    (hk : k < Extracted.program.data.length) {x l a n : Nat}
    (hin : (Extracted.program.data[k]).base ≤ x ∧
      x + l ≤ (Extracted.program.data[k]).base + (Extracted.program.data[k]).bytes.length)
    (hw : m.accessible a n true = true) : Apart x l a n := by
  have := Janus.Tactic.disjoint_of_dataLoaded hd k hk hw
  unfold Apart; omega

end FvModexp.Arm64

namespace FvModexp.Arm64

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- The live set apart from the window is apart from its two `winA` parts. -/
theorem liveSep_winA {L : List (Nat × Nat)} {s : State} {stk above : Nat} (h : LiveSep L (win s stk above)) :
    LiveSep L (winA s stk above) := by
  intro r hr
  have := h r hr
  simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
  omega

/-- The runtime invariant survives a frame inside the window (which is outside `R.rt`). -/
theorem inv_frame_winA {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {s : State} {m m' : Memory} {stk above : Nat}
    (hF : MemFrame m m' (winA s stk above)) (hout : Outside (s.sp.toNat - stk) (stk + above) R.rt)
    (hsp : stk ≤ s.sp.toNat) (h8 : 8 ≤ above) (hi : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') := by
  refine RtInv.inv_frame' hF (fun r hr => ?_) hi
  simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
  left
  rcases hr with rfl | rfl
  · exact hout.of_sub (Nat.le_refl _) (by simp; omega)
  · exact hout.of_sub (by simp; omega) (by simp; omega)

end FvModexp.Arm64
