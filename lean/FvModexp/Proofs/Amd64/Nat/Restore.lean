import FvModexp.Proofs.Amd64.Conv

/-!
# The open-coded `defer stk.restore(stk.save())` closures of the mul/div layer (amd64): the statement

As `Arm64/Nat/Restore.lean` (copied from agent expmc's `Amd64/Exp/Defer.lean`, same code shape). The closure
(context register `RDX` = the funcval `{fn, stk, n}`):

```
PUSHQ BP; MOVQ SP, BP
MOVQ 0x10(DX), AX        ; n
MOVQ 0x8(DX), CX         ; stk
MOVQ 0x10(CX), DX        ; cap(stk.w)
CMPQ DX, AX; JB panicBounds
MOVQ AX, 0x8(CX)         ; stk.w = stk.w[:n]
POPQ BP; RET
```
Each caller re-runs the one-`janus64_run` proof on its own library program (`BasicSqrDfr.dsum`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.Restore

/-- The context of a call of a `stk.restore` closure. -/
def Pre (s : State) : Prop :=
  StackWritable s 8 8 ∧ (s.regs 4).toNat % 8 = 0 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    (s.regs 2).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 2).toNat + 8) 16 false = true ∧
    s.mem.readLE ((s.regs 2).toNat + 8) 8 + 24 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 2).toNat + 8) 8) 24 true = true ∧
    s.mem.readLE ((s.regs 2).toNat + 16) 8 ≤ s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 2).toNat + 8) 8) 24 ((s.regs 4).toNat - 8) 16 ∧
    Apart ((s.regs 2).toNat + 8) 16 ((s.regs 4).toNat - 8) 16

/-- What it guarantees (`RSP` popped, `RBP`, `R14`, `X15` kept). -/
@[reducible] def Post (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.fsBase = s.fsBase ∧
    s'.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 = s.mem.readLE ((s.regs 2).toNat + 16) 8 ∧
    MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat),
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16)]

end FvModexp.Amd64.Restore
