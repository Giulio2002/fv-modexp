import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivLargeDefs
import FvModexp.Proofs.Arm64.Nat.Callees2

set_option autoImplicit false

/-!
# `divLarge` (arm64): the callees, moved into `LibDivL.program`

`lshVU.abi0` / `rshVU.abi0` (asm's library summaries, `Callees2`, with the runtime invariant carried over), `divBasic`
(its `ens`, `Ensures.toSummaryIn`), `divRecursiveStep` (premise `DrsHyp`), `(*stack).nat` (premise), the deferred closure
`nat.divLarge.deferwrap1` (`Restore`'s proof re-run on this program).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivLarge

theorem lshvu (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivL.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L) (LshLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact LshVUHyp.live (Summary.of_codeIn c (lshVUHyp impl hap)) R b L

theorem rshvu (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivL.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L) (RshLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [rshVUfn]).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact RshVUHyp.live (Summary.of_codeIn c (rshVUHyp impl hap)) R b L

set_option linter.defProp false in
/-- `divBasic`'s `ens` as a summary in `LibDivL.program.link impl` -/
def dbsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :=
  Ensures.toSummaryIn (DivBasic.ensL impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl vc)
    (noExit_restrict hap DivBasic.names)
    (show CodeIn ((Extracted.program.onlySegments DivBasic.names).link impl) (LibDivL.program.link impl) by
      rw [LibDivL.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide)))

set_option linter.defProp false in
/-- `divRecursiveStep`'s `Ensures` (premise) as a summary in `LibDivL.program.link impl` -/
def drssum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc vp vl vc d : BitVec 64) :=
  Ensures.toSummaryIn (hD b L qp ql qc st up ul uc vp vl vc d) (noExit_restrict hap drsNames)
    (show CodeIn ((Extracted.program.onlySegments drsNames).link impl) (LibDivL.program.link impl) by
      rw [LibDivL.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide)))

/-- `nat.divLarge.deferwrap1` -/
def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`Restore.sum`'s proof on this program) -/
theorem dsum (impl : List Segment) :
    Summary (LibDivL.program.link impl) 1810160 Restore.Pre Restore.Post := by
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

theorem pw_forall {α : Type} {R : α → α → Prop} (hR : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a}, a ∈ l → ∀ {b}, b ∈ l → a ≠ b → R a b
  | [], _, _, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, h, a, ha, b, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 _ hb'
    · exact hR (h.1 _ ha')
    · exact pw_forall hR h.2 ha' hb' hne

set_option maxRecDepth 20000 in
/-- a return site inside `divLarge`'s segment is admissible for a callee program that does not keep `divLarge` -/
theorem raL (impl : List Segment) (hap : ImplApart Extracted.program impl) (ns : List String)
    (hn : ns.contains fn = false) (ret : Nat) (hal : ret % 4 = 0) (h1 : 0x1b9950 ≤ ret) (h2 : ret < 0x1b9ef0)
    (hst : ∀ st ∈ Extracted.program.stubs, st.addr ≠ ret) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) ret := by
  have hmem : Extracted.seg27 ∈ Extracted.program.segments := by
    have : Extracted.program.segments[27]'(by decide) = Extracted.seg27 := rfl
    rw [← this]; exact List.getElem_mem _
  have hb : Extracted.seg27.base = 0x1b9950 := rfl
  have hl : Extracted.seg27.words.length = 360 := rfl
  have hnm : Extracted.seg27.name = fn := rfl
  refine RetAddr.of_placement hal (by omega) ⟨_, hmem, by rw [hb]; omega, by rw [hb, hl]; omega⟩ hap.1 ?_ hst
  intro seg hm hc
  by_cases he : seg = Extracted.seg27
  · subst he; rw [hnm, hn] at hc; exact absurd hc (by decide)
  · have hpw := (List.pairwise_append.1 hap.1).1
    have := pw_forall (fun {a b} h => by unfold Segment.Apart at h ⊢; omega) hpw hm hmem he
    unfold Segment.Apart at this; rw [hb, hl] at this; omega

end FvModexp.Arm64.DivLarge
