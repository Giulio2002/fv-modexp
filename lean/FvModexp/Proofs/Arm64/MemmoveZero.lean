import Janus

/-! # `memmove` with `n = 0` (arm64) — local copy of Janus PR #2's contract

Copied VERBATIM (definition text) from Janus PR #2 (github.com/Giulio2002/Janus/pull/2, branch
fix/memmove-zero-contract @ 862c3789, `Janus/Contracts/Live.lean` `MemmoveZeroLive`), because fv-modexp
is still pinned to Janus v0.2.0. Once the pin moves to a release containing PR #2, this file is deleted
and `FvModexp.Arm64.MemmoveZeroLive` is replaced by `Janus.Contracts.MemmoveZeroLive` (same text).

It is a PREMISE (a pinned runtime contract) of the theorems that use it, exactly like `MemmoveLive`;
it is not assumed anywhere. Justification (PR #2): the pinned go1.26.x `runtime.memmove` returns at its
first instruction when `n = 0` (`CBZ R2, copy0; … copy0: RET`), touching no memory. -/

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64

/-- **`runtime.memmove(dst, src, 0)`, live** (`X0 = dst`, `X1 = src`, `X2 = n = 0`): Janus PR #2's
`MemmoveZeroLive`, verbatim. -/
def MemmoveZeroLive (p : Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (s.regs 2).toNat = 0 ∧ Mem.EqPre d 3 s ∧
      LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3))
    (fun s s' => LiveMemRet R d 3 [] L b s s' fun _ => True)

theorem MemmoveZeroLive.of_codeIn {p P : Program} (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : MemmoveZeroLive p a d R) : MemmoveZeroLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)

end FvModexp.Arm64
