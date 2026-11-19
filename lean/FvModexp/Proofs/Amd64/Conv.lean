import Extracted
import FvModexp.Proofs.Common.Conv

/-!
# Conventions for function summaries (amd64)

See `docs/history/CONVENTIONS-v2.md`. As `FvModexp.Arm64.CallEnv`, for the amd64 Go ABIInternal: `RSP = s.regs 4`, `g = R14`.
The window `[RSP - stk, RSP + above)` includes the return-address slot `[RSP, RSP + 8)` (take `above ≥ 8`).
-/

namespace FvModexp.Amd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

/-- The stack window of a summary: `[RSP - stk, RSP + above)`. -/
@[reducible] def win (s : State) (stk above : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - stk, (s.regs 4).toNat + above)]

/-- The extraction's read-only data lies outside the runtime-owned ranges (`FvModexp.dataLoaded_frame64`). -/
def RoOut (R : RtInv) : Prop := ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt

/-- The goroutine pointer in TLS (Go reloads `R14` from `FS:-8` after every ABI0 assembly call): the slot is readable, holds
`R14`, lies outside the runtime-owned ranges and apart from the window (NOTES-divmc issue 4). -/
def TlsOK (R : RtInv) (s : State) (stk above : Nat) : Prop :=
  TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 R.rt ∧ Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - stk) (stk + above)

/-- The call environment of a summary (amd64): the stack-growth prologues fall through, `RSP` 8-aligned, the window
writable, the read-only data loaded, the window and the `stackguard0` slot outside the runtime-owned ranges and apart,
no live object in the window. -/
def CallEnv (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  StackGuardOK s stk ∧ StackWritable s stk above ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - stk) (stk + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above) ∧ RoOut R ∧ TlsOK R s stk above

/-- The address of a runtime contract of the extraction. -/
@[reducible] def cA (name : String) : Nat := Extracted.program.contractAddr name

end FvModexp.Amd64

namespace FvModexp.Amd64

open Janus Janus.Amd64

/-- A read-only data object (`x`, `l` inside data object `k`) is apart from every writable range (amd64; see the arm64
twin: never `janus64_data hd [hw]` on the Run extraction). -/
theorem apart_of_data {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) (k : Nat)
    (hk : k < Extracted.program.data.length) {x l a n : Nat}
    (hin : (Extracted.program.data[k]).base ≤ x ∧
      x + l ≤ (Extracted.program.data[k]).base + (Extracted.program.data[k]).bytes.length)
    (hw : m.accessible a n true = true) : Apart x l a n := by
  have := Janus.Amd64.Tactic.disjoint_of_dataLoaded hd k hk hw
  unfold Apart; omega

end FvModexp.Amd64

namespace FvModexp.Amd64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts

/-- A read-only data object (`x`, `l` inside data object `k`) is outside the runtime-owned ranges. -/
theorem RoOut.out' {R : RtInv} (h : RoOut R) (k : Nat) (hk : k < Extracted.program.data.length) {x l : Nat}
    (hin : (Extracted.program.data[k]).base ≤ x ∧
      x + l ≤ (Extracted.program.data[k]).base + (Extracted.program.data[k]).bytes.length) : Outside x l R.rt :=
  (h _ (List.getElem_mem hk)).of_sub hin.1 hin.2

end FvModexp.Amd64
