import FvModexp.Proofs.Amd64.Nat.StackNatG

/-!
# `(*stack).nat` (go-bigmodexpfix nat.go:319), amd64: the summary

As the arm64 twin (Arm64/Nat/StackNat.lean): `full` (`len + nr ≤ cap`: `noGrow`; else `grow`), `ens` (CONVENTIONS §3),
`hyp` (the premise form `Hyp impl R names 4192 24`), `sum`. Runtime contracts: live `growslice`,
`memclrNoHeapPointers`, `gcWriteBarrier2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.StackNat

theorem GrowsliceLiveContract64.of_codeIn {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : GrowsliceLiveContract64 p a st R) : GrowsliceLiveContract64 P a st R :=
  fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (h L b)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Summary (LibStackNat.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = st ∧ s.regs 3 = n ∧ Pre R b L 4192 24 st.toNat n.toNat s)
      (fun s s' => RegsOK s s' ∧ Post R b L 4192 24 st.toNat n.toNat s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, hpre⟩
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibStackNat.program.link impl) := by
    rw [LibStackNat.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap names
  by_cases hk : stLen s.mem st.toNat + rnd n.toNat ≤ stCap s.mem st.toNat
  · exact noGrow impl R (WbLiveContract64.of_codeIn hc hwb) b L st n s hpc hra hx15 hdf h0 h3 hpre hk
  · exact grow impl R (GrowsliceLiveContract64.of_codeIn hc hgr) (MemclrNoHeapPointersLive64.of_codeIn hc hmc)
      (WbLiveContract64.of_codeIn hc hwb) b L st n s hpc hra hx15 hdf h0 h3 hpre (by omega)

/-- **`(*stack).nat`** (amd64): as `FvModexp.Arm64.StackNat.ens` (results `RAX, RBX, RCX`, `fsBase` kept). -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => Pre R b L 4192 24 st.toNat n.toNat s) (fun s s' => Post R b L 4192 24 st.toNat n.toNat s s') := by
  rw [show names = LibStackNat.names from rfl, ← LibStackNat.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hgr hmc hwb b L st n) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- `ens` in the premise form `Hyp`. -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    Hyp impl R names 4192 24 := fun b L st n => ens impl hap R hgr hmc hwb b L st n

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hgr hmc hwb b L st n) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.StackNat
