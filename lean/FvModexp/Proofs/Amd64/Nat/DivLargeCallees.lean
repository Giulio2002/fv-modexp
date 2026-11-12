import FvModexp.Proofs.Amd64.Nat.DivLargeDefs
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Amd64.Nat.RshCallee
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `divLarge` (amd64): the callees, moved into `LibDivL.program`

The twin of `Arm64/Nat/DivLargeCallees.lean`: `lshVU.abi0` / `rshVU.abi0` (asm's library summaries with the runtime
invariant carried over), `divBasic` (top's `DivBasic.sumL`), `divRecursiveStep` (premise `DrsHyp`), the deferred closure
`nat.divLarge.deferwrap1` (`Restore`'s proof re-run on this program).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivLarge

theorem lshvu (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivL.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L) (LshLQ R b L) := by
  have c : CodeIn64 ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  exact LshVUHyp.live (Summary.of_codeIn64 c (lshVUHyp impl hap)) R b L

theorem rshvu (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivL.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L) (RshLQ R b L) := by
  have c : CodeIn64 ((Extracted.program.onlySegments [rshVUfn]).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  exact RshVUHyp.live (Summary.of_codeIn64 c (rshVUHyp impl hap)) R b L

set_option linter.defProp false in
/-- `divBasic`'s `ensL` as a summary in `LibDivL.program.link impl` -/
def dbsum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) :=
  Ensures.toSummaryIn (DivBasic.ensL impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl)
    (A64.noExit_restrict64 hap DivBasic.names) (by simp [numIntRegs])
    (show CodeIn64 ((Extracted.program.onlySegments DivBasic.names).link impl) (LibDivL.program.link impl) by
      rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide)))

set_option linter.defProp false in
/-- `divRecursiveStep`'s `Ensures` (premise) as a summary in `LibDivL.program.link impl` -/
def drssum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat) :=
  Ensures.toSummaryIn (hD b L qp ql qc st up ul uc d vp vl vc) (A64.noExit_restrict64 hap drsNames)
    (by simp [numIntRegs])
    (show CodeIn64 ((Extracted.program.onlySegments drsNames).link impl) (LibDivL.program.link impl) by
      rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide)))

/-- `nat.divLarge.deferwrap1` -/
def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1"

/-- the address of the closure `nat.divLarge.deferwrap1` (`LEAQ …(SB), R12` at `+0x84`) -/
abbrev dfnL : Nat := 6222240

theorem dfnL_eq : segAddr LibDivL.program fnD = dfnL := by decide

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`Restore`'s proof on this program) -/
theorem dsum (impl : List Amd64.Segment) :
    Summary (LibDivL.program.link impl) dfnL Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

end FvModexp.Amd64.DivLarge
