import FvModexp.Proofs.Arm64.Nat.BasicSqrStep
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `basicSqr` (arm64): the deferred `stk.restore(stk.save())` closure as a callee of `LibBasicSqr`

`Restore.sum` is proved on `LibRestore.program` (all seven closures); the closure `basicSqr.deferwrap1` is re-run here on
`LibBasicSqr.program` (same proof, one `janus_run`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicSqr

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr.deferwrap1"

set_option maxRecDepth 20000 in
theorem dsum (impl : List Segment) :
    Summary (LibBasicSqr.program.link impl) (segAddr LibBasicSqr.program fnD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnD, reduceSegAddr] at hpc
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

end FvModexp.Arm64.BasicSqr
