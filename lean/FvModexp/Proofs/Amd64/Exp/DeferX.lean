import FvModexp.Proofs.Amd64.Exp.Defer
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.MontW

set_option autoImplicit false

/-!
# The `stk.restore` defer closures (amd64): `Defer.Post` + `fsBase`/`DF` kept, as a summary of `LibW` (agent expmc s47)

`Defer.sum` (on `LibDefer`) does not state `s'.fsBase = s.fsBase ∧ s'.df = s.df`, which every amd64 caller needs after
the call (AMD64 DF CONVENTION). `sumX` proves the closure again with them and lifts it to the window layer's program
`LibW` (`LibDefer ⊆ LibW`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.Defer

/-- `Post` with `fsBase` and `DF` kept -/
def PostX (s s' : State) : Prop := Post s s' ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df

set_option maxRecDepth 20000 in
theorem sumX0 (impl : List Amd64.Segment) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"]) :
    Summary (LibDefer.program.link impl) (segAddr LibDefer.program fn) Pre PostX := by
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
    refine ⟨⟨?_, rfl, rfl, rfl, ?_, by janus_frame⟩, rfl, rfl⟩
    · simp [setRegF]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    simp only [Nat.reducePow]
    have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
    omega

/-- `sumX0` as a summary of the window layer's program -/
theorem sumX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"]) :
    Summary (LibW.program.link impl) (segAddr LibW.program fn) Pre PostX := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibW.names.contains x = true :=
    MontW.sub_of_all (by decide)
  have hc := A64.codeIn_restrict_mono64 hap hsub
  rw [← LibDefer.eq_only, ← LibW.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (sumX0 impl fn hfn)
  have e : segAddr LibDefer.program fn = segAddr LibW.program fn := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e] at h
  exact h

end FvModexp.Amd64.Defer
