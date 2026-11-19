import FvModexp.Proofs.Arm64.Nat.StackNatXG

set_option autoImplicit false

/-!
# `(*stack).nat` (go-bigmodexpfix nat.go:319), arm64: the EXACT-budget and Q-form summaries (divmc, TIGHT COSTS)

As `StackNat` (same proof, copied chain `StackNatX*`), with `StackNatXDefs`' exact budget: `ensX` (`PreX`/`PostXL`),
`ensQ`/`hypQ`/`sumQ` (the Q-form of Common/StackPot: amortised growth). Runtime contracts: live `growslice`,
`memclrNoHeapPointers`, `gcWriteBarrier2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.StackNatX

open FvModexp.Arm64.StackNat (fn names wbA rnd)


theorem GrowsliceLiveContract.of_codeIn' {p P : Program} (hc : CodeIn p P) {a st : Nat} {R : RtInv}
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
        PreX R b L 4208 24 st.toNat n.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostXL R b L 4208 24 st.toNat n.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, hpre⟩
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibStackNat.program.link impl) := by
    rw [LibStackNat.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap names
  by_cases hk : stLen s.mem st.toNat + rnd n.toNat ≤ stCap s.mem st.toNat
  · exact noGrow impl R (WbLiveContract.of_codeIn hc hwb) b L st n s hpc hl4 hl48 h0 h1 hpre hk
  · exact grow impl R (GrowsliceLiveContract.of_codeIn' hc hgr) (MemclrNoHeapPointersLive.of_codeIn hc hmc)
      (WbLiveContract.of_codeIn hc hwb) b L st n s hpc hl4 hl48 h0 h1 hpre (by omega)

/-- **`(*stack).nat`**, L form (`PostL`: a grown array is an element of the final live set) (arm64): `stk.nat(n)` returns `n` words at `w' + 8·len` (the stack's array, grown by `growslice`
when `cap < len + nr`), the stack's `len` advanced by `nr = (n + 3) &^ 3`; writes only the header, the old array's free
part, `R.rt` and the window; no panic, no fault. -/
theorem ensX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => PreX R b L 4208 24 st.toNat n.toNat s) (fun s s' => PostXL R b L 4208 24 st.toNat n.toNat s s') := by
  janus_ensures_old [FvModexp.Arm64.StackNatX.PreX, FvModexp.Arm64.CallEnv, FvModexp.StkOK, FvModexp.Arm64.win, FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Arm64.StackNat.wbA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.NatLive]
  rw [show names = LibStackNat.names from rfl, ← LibStackNat.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hgr hmc hwb b L st n) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- **`(*stack).nat`, Q-form** (arm64): as `ensX`, the budget amortised (Common/StackPot): pre `len + n + 3 ≤ H`,
`stkR H ≤ b`; post `b - stkR H s.mem st + stkR H s'.mem st ≤ b'`. -/
theorem ensQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => PreQ R b L H 4208 24 st.toNat n.toNat s) (fun s s' => PostQ R b L H 4208 24 st.toNat n.toNat s s') := by
  refine Ensures.mono (hinv := by janus_pre_setRet [FvModexp.Arm64.StackNatX.PreQ, FvModexp.Arm64.CallEnv, FvModexp.StkOK, FvModexp.Arm64.win, FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.stkR, FvModexp.Arm64.StackNat.wbA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.NatLive, FvModexp.stkRes, FvModexp.potK]) (ensX impl hap R hgr hmc hwb b L st n) (fun s h => preX_of_preQ h) ?_
  intro s s' hq hp
  exact PostXL.toPostQ hq.2.2.2.2.2.2.2.1.1 hq.2.2.2.2.2.2.2.1.2 hp

/-- `ensQ` in the premise form `HypQ` -/
theorem hypQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    HypQ impl R names 4208 24 := fun H b L st n => ensQ impl hap R hgr hmc hwb H b L st n

set_option linter.defProp false in
/-- `ensQ` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sumQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ensQ impl hap R hgr hmc hwb H b L st n) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.StackNatX
