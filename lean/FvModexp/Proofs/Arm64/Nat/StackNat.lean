import FvModexp.Proofs.Arm64.Nat.StackNatG

/-!
# `(*stack).nat` (go-bigmodexpfix nat.go:319), arm64: the summary

`full`: the `Summary` at the entry (`len + nr ≤ cap`: `noGrow`; else `grow`). `ens`: the `Ensures` of CONVENTIONS §3 on
`(Extracted.program.onlySegments names).link impl` (= agent expmc's `ExpHyp.StackNatHyp` shape, amended — see
StackNatDefs); `sum`: `ens` as a callee summary; `hyp`: `Hyp impl R names 4208 24` (the premise form callers take).
Runtime contracts: live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.StackNat

theorem GrowsliceLiveContract.of_codeIn {p P : Program} (hc : CodeIn p P) {a st : Nat} {R : RtInv}
    (h : GrowsliceLiveContract p a st R) : GrowsliceLiveContract P a st R :=
  fun L b => Summary.of_codeIn hc (h L b)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Summary (LibStackNat.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = st ∧ s.regs 1 = n ∧
        Pre R b L 4208 24 st.toNat n.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostL R b L 4208 24 st.toNat n.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, hpre⟩
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibStackNat.program.link impl) := by
    rw [LibStackNat.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap names
  by_cases hk : stLen s.mem st.toNat + rnd n.toNat ≤ stCap s.mem st.toNat
  · exact noGrow impl R (WbLiveContract.of_codeIn hc hwb) b L st n s hpc hl4 hl48 h0 h1 hpre hk
  · exact grow impl R (GrowsliceLiveContract.of_codeIn hc hgr) (MemclrNoHeapPointersLive.of_codeIn hc hmc)
      (WbLiveContract.of_codeIn hc hwb) b L st n s hpc hl4 hl48 h0 h1 hpre (by omega)

/-- **`(*stack).nat`**, L form (`PostL`: a grown array is an element of the final live set) (arm64): `stk.nat(n)` returns `n` words at `w' + 8·len` (the stack's array, grown by `growslice`
when `cap < len + nr`), the stack's `len` advanced by `nr = (n + 3) &^ 3`; writes only the header, the old array's free
part, `R.rt` and the window; no panic, no fault. -/
theorem ensL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => Pre R b L 4208 24 st.toNat n.toNat s) (fun s s' => PostL R b L 4208 24 st.toNat n.toNat s s') := by
  rw [show names = LibStackNat.names from rfl, ← LibStackNat.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hgr hmc hwb b L st n) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- **`(*stack).nat`** (arm64): `stk.nat(n)` returns `n` words at `w' + 8·len` (the stack's array, grown by `growslice`
when `cap < len + nr`), the stack's `len` advanced by `nr = (n + 3) &^ 3`; writes only the header, the old array's free
part, `R.rt` and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => Pre R b L 4208 24 st.toNat n.toNat s) (fun s s' => Post R b L 4208 24 st.toNat n.toNat s s') := by
  rw [show names = LibStackNat.names from rfl, ← LibStackNat.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hgr hmc hwb b L st n) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, PostL.toPost hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- `ens` in the premise form `Hyp` (agent expmc's `ExpHyp.StackNatHyp`). -/
theorem hyp (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    Hyp impl R names 4208 24 := fun b L st n => ens impl hap R hgr hmc hwb b L st n

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hgr hmc hwb b L st n) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

/-- `ensL` in the premise form `HypL` -/
theorem hypL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    HypL impl R names 4208 24 := fun b L st n => ensL impl hap R hgr hmc hwb b L st n

set_option linter.defProp false in
/-- `ensL` as a callee summary (as `sum`) -/
def sumL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ensL impl hap R hgr hmc hwb b L st n) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.StackNat
