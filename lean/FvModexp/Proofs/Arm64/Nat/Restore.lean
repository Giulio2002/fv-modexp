import FvModexp.Proofs.Arm64.Nat.LibRestore
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# The open-coded `defer stk.restore(stk.save())` closures of the mul/div layer (arm64)

(copied from agent expmc's `Arm64/Exp/Defer.lean`, same code shape; divmc's closures: basicSqr, karatsuba, karatsubaSqr,
nat.mul (`deferwrap2`), divBasic, divLarge, divRecursiveStep)

`nat.expNNEven`, `expNNOddMontgomeryWindowSize{4,2}`, `expNNPowerOfTwoWindowSize{4,2}` each defer
`stk.restore(stk.save())` (nat.go:303-316): the compiler builds a closure `…deferwrap1` capturing `stk` (`*stack`) and
`n = len(stk.w)` at the defer, and calls it at every exit. (`nat.expNN.deferwrap1` is a different closure: it returns `stk` to `stackPool`
through `sync.(*Pool).Put`; it belongs with the Pool contracts.) Its code (all five identical up to addresses):

```
ldp x0, x1, [x26, #8]    ; x0 = stk, x1 = n (the captured variables, after the code pointer of the funcval)
ldr x2, [x0, #16]        ; cap(stk.w)
cmp x2, x1 ; b.lo panicBounds
str x1, [x0, #8]         ; stk.w = stk.w[:n]  (only len changes)
```

**Summary** (`sum fn`): from any entry state whose context register `X26` points at a readable closure, whose captured
`stk` points at a writable 24-byte slice header with `n ≤ cap(stk.w)`, the closure returns (no panic) with `SP`, `g`,
`FP`, `R18` kept, `len(stk.w) = n`, and memory changed only in its frame `[SP-24, SP-8)` (the caller's saved `X29` at `SP-8` is kept) and the `len` word.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Restore

/-- The context of a call of a `stk.restore` closure. -/
def Pre (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 24 0 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (s.regs 26).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 26).toNat + 8) 16 false = true ∧
    s.mem.readLE ((s.regs 26).toNat + 8) 8 + 24 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 26).toNat + 8) 8) 24 true = true ∧
    s.mem.readLE ((s.regs 26).toNat + 16) 8 ≤ s.mem.readLE (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 26).toNat + 8) 8) 24 (s.sp.toNat - 24) 24 ∧
    Apart ((s.regs 26).toNat + 8) 16 (s.sp.toNat - 24) 24

/-- What it guarantees. -/
@[reducible] def Post (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    s'.mem.readLE (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8) 8 = s.mem.readLE ((s.regs 26).toNat + 16) 8 ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - 24, s.sp.toNat - 8),
      (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 26).toNat + 8) 8 + 16)]

set_option maxRecDepth 20000 in
theorem sum (impl : List Segment) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap2",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep.deferwrap1"]) :
    Summary (LibRestore.program.link impl) (segAddr LibRestore.program fn) Pre Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [reduceSegAddr] at hpc
    janus_run
    refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    simp only [Nat.reducePow]
    have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
    omega

end FvModexp.Arm64.Restore
