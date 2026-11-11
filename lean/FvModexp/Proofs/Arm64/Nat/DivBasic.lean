import FvModexp.Proofs.Arm64.Nat.DivBasicLoop
import FvModexp.Proofs.Arm64.Nat.DivBasicNat
import FvModexp.Proofs.Arm64.Nat.DivBasicRec
/-!
# `(q nat) divBasic(stk *stack, u, v nat)` (go-bigmodexpfix natdiv.go:646), arm64: the summary

`full`: the `Summary` at the entry (`pro1` → `pro2` (`stk.nat`, premise `ExpHyp.StackNatHyp`) → `pro3`
(`reciprocalWord`) → `fromHead` (loop, exit, deferred `stk.restore`, return)); `ens`: the `Ensures` of CONVENTIONS §3 with
the `(*stack).nat` premise discharged by `StackNat.hyp` (stk 4208, above 24) — premises are live runtime contracts only;
`sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivBasic

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : ExpHyp.StackNatHyp impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :
    Summary (LibDivBasic.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = qp ∧ s.regs 1 = ql ∧ s.regs 2 = qc ∧ s.regs 3 = st ∧ s.regs 4 = up ∧ s.regs 5 = ul ∧
        s.regs 6 = uc ∧ s.regs 7 = vp ∧ s.regs 8 = vl ∧ s.regs 9 = vc ∧
        Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
      (fun s s' => RQ R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp.toNat vl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpre⟩
  exact pro1 impl R b L qp ql qc st up ul uc vp vl vc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre _ fun P hP hinvP =>
    pro2 impl hap R stkSN abSN hSN hk1 hk2 b L qp ql st up ul uc vp vl vc s hpre P hP hinvP _ fun S2 L1 b1 hA =>
      pro3 impl hap R stkSN abSN hk1 hk2 b L qp ql st up ul uc vp vl vc s hpre P hP S2 L1 b1 hA _
        fun S t w1 c1 hH hqu => fromHead impl hap R b L _ _ _ _ _ _ _ _ vc.toNat s t L1 b1 w1 c1 S hH hqu hl4 hl48

/-- **`divBasic`** (arm64): `q = divBasic(stk, u, v)` (normalised `v`, `2 ≤ len v`, room for the quotient) stores
`U / V` in `q[0 : qn]` (when `len v ≤ len u`) and `U mod V` in `u` in place, restores the stack's `len`; writes only
`q[0 : qn]`, `u`, the stack header and free part, the runtime's memory and the window; no panic, no fault. Premises:
the live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2` contracts (through `(*stack).nat`). -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc]
      (Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat)
      (Post R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp.toNat vl.toNat) := by
  rw [show names = LibDivBasic.names from rfl, ← LibDivBasic.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R 4208 24 (StackNat.hyp impl hap R hgr hmc hwb) (by decide) (by decide)
    b L qp ql qc st up ul uc vp vl vc) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl vc)
    (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.DivBasic
