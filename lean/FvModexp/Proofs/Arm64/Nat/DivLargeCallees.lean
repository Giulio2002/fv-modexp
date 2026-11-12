import FvModexp.Proofs.Arm64.Nat.DivLargeDefs
import FvModexp.Proofs.Arm64.Nat.Callees2

/-!
# `divLarge` (arm64): the callees, moved into `LibDiv.program`

`lshVU.abi0` / `rshVU.abi0` (asm's library summaries, `Callees2`, with the runtime invariant carried over), `divBasic`
(its `ens`, `Ensures.toSummaryIn`), `divRecursiveStep` (premise `DrsHyp`), `(*stack).nat` (premise), the deferred closure
`nat.divLarge.deferwrap1` (`Restore`'s proof re-run on this program).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivLarge

theorem lshvu (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDiv.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L) (LshLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibDiv.program.link impl) := by
    rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact LshVUHyp.live (Summary.of_codeIn c (lshVUHyp impl hap)) R b L

theorem rshvu (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDiv.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L) (RshLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [rshVUfn]).link impl) (LibDiv.program.link impl) := by
    rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact RshVUHyp.live (Summary.of_codeIn c (rshVUHyp impl hap)) R b L

set_option linter.defProp false in
/-- `divBasic`'s `ens` as a summary in `LibDiv.program.link impl` -/
def dbsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :=
  Ensures.toSummaryIn (DivBasic.ens impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl vc)
    (noExit_restrict hap DivBasic.names)
    (show CodeIn ((Extracted.program.onlySegments DivBasic.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide)))

set_option linter.defProp false in
/-- `divRecursiveStep`'s `Ensures` (premise) as a summary in `LibDiv.program.link impl` -/
def drssum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc vp vl vc d : BitVec 64) :=
  Ensures.toSummaryIn (hD b L qp ql qc st up ul uc vp vl vc d) (noExit_restrict hap names)
    (show CodeIn ((Extracted.program.onlySegments names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (fun _ h => h))

/-- `nat.divLarge.deferwrap1` -/
def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`Restore.sum`'s proof on this program) -/
theorem dsum (impl : List Segment) :
    Summary (LibDiv.program.link impl) 1810160 Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

end FvModexp.Arm64.DivLarge
