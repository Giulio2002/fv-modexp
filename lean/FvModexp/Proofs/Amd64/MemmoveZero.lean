import Janus

/-! # `memmove` with `n = 0` (amd64) — local copy of Janus PR #2's contract

Copied VERBATIM (definition text) from Janus PR #2 (github.com/Giulio2002/Janus/pull/2, branch
fix/memmove-zero-contract @ 862c3789, `Janus/Contracts/LiveAmd64.lean` `MemmoveZeroLive64`), because
fv-modexp is still pinned to Janus v0.2.0; replaced by `Janus.Contracts.MemmoveZeroLive64` on re-pin.
A PREMISE (pinned runtime contract), like `MemmoveLive64`. Justification (PR #2): the pinned go1.26.x
`runtime.memmove` returns before any memory access when `n = 0` (`TESTQ BX, BX; JEQ move_0`). -/

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64

/-- **`runtime.memmove(dst, src, 0)`, live** (amd64; `RAX = dst`, `RBX = src`, `RCX = n = 0`):
Janus PR #2's `MemmoveZeroLive64`, verbatim. -/
def MemmoveZeroLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (s.regs 1).toNat = 0 ∧ MemPre64 d 3 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s d 3))
    (fun s s' => LiveMemRet64 R d 3 [] L b s s' fun _ => True)

theorem MemmoveZeroLive64.of_codeIn {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {a d : Nat} {R : RtInv}
    (h : MemmoveZeroLive64 p a d R) : MemmoveZeroLive64 P a d R :=
  fun L b => Summary.of_codeIn64 hc (h L b)

end FvModexp.Amd64
