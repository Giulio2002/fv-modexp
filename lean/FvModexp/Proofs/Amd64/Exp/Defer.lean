import FvModexp.Proofs.Amd64.Exp.LibDefer
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# The open-coded `defer stk.restore(stk.save())` closures (amd64; see the arm64 twin)

```
PUSHQ BP; MOVQ SP, BP
MOVQ 0x10(DX), AX        ; n   (DX = the closure context)
MOVQ 0x8(DX), CX         ; stk
MOVQ 0x10(CX), DX        ; cap(stk.w)
CMPQ DX, AX; JB panicBounds
MOVQ AX, 0x8(CX)         ; stk.w = stk.w[:n]
POPQ BP; RET
```
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.Defer

/-- The context of a call of a `stk.restore` closure (`RDX` = the funcval). -/
def Pre (s : State) : Prop :=
  StackWritable s 8 8 ∧ (s.regs 4).toNat % 8 = 0 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    (s.regs 2).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 2).toNat + 8) 16 false = true ∧
    s.mem.readLE ((s.regs 2).toNat + 8) 8 + 24 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 2).toNat + 8) 8) 24 true = true ∧
    s.mem.readLE ((s.regs 2).toNat + 16) 8 ≤ s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 2).toNat + 8) 8) 24 ((s.regs 4).toNat - 8) 16 ∧
    Apart ((s.regs 2).toNat + 8) 16 ((s.regs 4).toNat - 8) 16

/-- What it guarantees (`RSP` popped, `RBP`, `R14`, `X15` kept). -/
def Post (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 = s.mem.readLE ((s.regs 2).toNat + 16) 8 ∧
    MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat),
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16)]

set_option maxRecDepth 20000 in
theorem sum (impl : List Amd64.Segment) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"]) :
    Summary (LibDefer.program.link impl) (segAddr LibDefer.program fn) Pre Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [reduceSegAddr] at hpc
    janus64_run
    refine ⟨?_, rfl, rfl, rfl, ?_, by janus_frame⟩
    · simp [setRegF]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    simp only [Nat.reducePow]
    have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
    omega

end FvModexp.Amd64.Defer
