import FvModexp.Proofs.Amd64.Nat.DivBasicLoop
import FvModexp.Proofs.Amd64.Nat.DivBasicNat
import FvModexp.Proofs.Amd64.Nat.DivBasicPro3
import FvModexp.Proofs.Amd64.Nat.StackNat

set_option autoImplicit false

/-!
# `(q nat) divBasic(stk *stack, u, v nat)` (go-bigmodexpfix natdiv.go:646), amd64: the summary

`full`: the `Summary` at the entry (`pro1` → `pro2` (`stk.nat`, premise `StackNat.HypL`) → `pro3` (inlined
`reciprocalWord`) → `fromHead` (loop, exit, deferred `stk.restore`, return)); `ensL`/`ens`: the `Ensures` of
CONVENTIONS §3 (register arguments `q, stk, u`; `v` is passed on the stack, `Pre.vpS`/`vlS`) with the `(*stack).nat`
premise discharged by `StackNat.hypL` — premises are live runtime contracts only; `sum`/`sumL`: as callee summaries.
The twin of `Arm64/Nat/DivBasic.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) :
    Summary (LibDivBasic.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = qp ∧ s.regs 3 = ql ∧ s.regs 1 = qc ∧ s.regs 7 = st ∧ s.regs 6 = up ∧ s.regs 8 = ul ∧
        s.regs 9 = uc ∧ Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s)
      (fun s s' => RQ R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  exact pro1 impl R b L qp ql qc st up ul uc vp vl s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre _ fun P hP hinvP =>
    pro2 impl hap R hSN b L qp ql st up ul uc vp vl s hpre P hP hinvP _ fun S2 L1 b1 hA =>
      pro3 impl R b L qp ql st up ul uc vp vl s hpre hx15 hdf hra P hP S2 L1 b1 hA _
        fun S t w1 c1 hH hqu => fromHead impl hap R b L _ _ _ _ _ _ _ _ _ s t L1 b1 w1 c1 S hH hqu

/-- **`divBasic`** (amd64): `q = divBasic(stk, u, v)` (normalised `v`, `2 ≤ len v`, room for the quotient) stores
`U / V` in `q[0 : qn]` (when `len v ≤ len u`) and `U mod V` in `u` in place, restores the stack's `len`; writes only
`q[0 : qn]`, `u`, the stack header and free part, the runtime's memory and the window; `fsBase` and `DF` kept; no
panic, no fault. Premises: the live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2` contracts (through
`(*stack).nat`). -/
theorem ensL (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [qp, ql, qc, st, up, ul, uc]
      (Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl)
      (PostL R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl) := by
  rw [show names = LibDivBasic.names from rfl, ← LibDivBasic.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R (StackNat.hypL impl hap R hgr hmc hwb) b L qp ql qc st up ul uc vp vl) hret
    (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
      h_a3, h_a4, h_a5, h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- `ensL` with the `StackBack` post -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [qp, ql, qc, st, up, ul, uc]
      (Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl)
      (Post R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl) :=
  (ensL impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl).mono (fun _ h => h) (fun _ _ _ h => h.toPost)

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

set_option linter.defProp false in
/-- `ensL` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sumL (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ensL impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.DivBasic
