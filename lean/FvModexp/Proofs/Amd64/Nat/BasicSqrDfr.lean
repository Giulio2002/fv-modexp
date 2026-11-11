import FvModexp.Proofs.Amd64.Nat.BasicSqrStep
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `basicSqr` (amd64): the deferred `stk.restore(stk.save())` closure as a callee of `LibBasicSqr`

The closure `basicSqr.deferwrap1` (`Restore.Pre`/`Restore.Post`, Amd64/Nat/Restore.lean), one `janus64_run` on
`LibBasicSqr.program` (the proof of agent expmc's `Amd64/Exp/Defer.lean`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.BasicSqr

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr.deferwrap1"

set_option maxRecDepth 20000 in
theorem dsum (impl : List Amd64.Segment) :
    Summary (LibBasicSqr.program.link impl) (segAddr LibBasicSqr.program fnD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnD, reduceSegAddr] at hpc
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

end FvModexp.Amd64.BasicSqr
