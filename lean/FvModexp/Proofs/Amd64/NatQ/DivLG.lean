import FvModexp.Proofs.Amd64.NatQ.Div
import FvModexp.Proofs.Amd64.NatQ.DivZOne
import FvModexp.Proofs.Amd64.NatQ.DivZOneA
import FvModexp.Proofs.Amd64.NatQ.DivZCmp
import FvModexp.Proofs.Amd64.NatQ.DivZTwo
import FvModexp.Proofs.Amd64.NatQ.DivZLess
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLG.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64): expmc's `ExpSlow.DivHypLG` (empty-tolerant dividend, results apart) — twin of `Arm64/Nat/DivLG.lean`

`fullZ`: `len u = 0` (`u` possibly `nil`): `len v = 1`: `one1G` → `one2Z` (`divW` via `DivW.ens0`) → `oneA`
(`r = z2[:0]`); `len v ≥ 2`: `two1G` → `two2G` (`cmp`, no limb of `u` read) → `U = 0 < V` → `lessRG` (`0 ≤ cap z2`)
→ `lessC0` (`MemmoveZeroLive64`). `ensLG`: `len u = 0` → `fullZ`; `len u > 0` → `PreG.toPre` → `full` (whose paths all
end in `RQG`). `ensDLG`: `divLarge` discharged (`DivLarge.ensG`), premise `DrsHyp`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
theorem fullZ (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hu : ul = 0) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = st ∧ s.regs 6 = z2 ∧ s.regs 8 = z2l ∧
        s.regs 9 = z2c ∧
        PreG R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
      (fun s s' => RQG R b H dc L zp.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hc3 := codeIn_lib impl hap
  have hmz := MemmoveZeroLive64.of_codeIn hc3 hmz0
  have hp := hpre.f
  have hU0 : natVal s.mem u ul = 0 := by simp only [natVal, hu, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
  by_cases hv1 : vl = 1
  · subst hv1
    refine one1G impl R b dc L zp zl zc st z2 z2l z2c u ul uc v vc s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre _
      fun X hX => one2Z impl hap R hmk0 hmv0 hmz0 b dc L zp zl zc st z2 z2l z2c u ul uc v vc s hpre hu X hX _
        fun q ql qc L' b' T hW => ?_
    exact oneA impl R hpre hW (by rw [hU0, Nat.zero_mod]) hra hx15 hdf
  · have hv2 : 2 ≤ vl := by have := hp.v0; omega
    refine two1G impl R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s hpc hx15 hdf h0 h3 h1 h7 h6 h8 h9 hv2 hpre _
      fun X hX => two2G impl hap R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s hpre X hX _ fun S hS => ?_
    have hV : 0 < natVal s.mem v vl := by
      rcases hp.vn with h | h
      · omega
      · have := natVal_ge1 s.mem v vl (by omega) h
        have := Nat.two_pow_pos (64 * (vl - 1)); omega
    have hU : natVal s.mem u ul < natVal s.mem v vl := by rw [hU0]; exact hV
    have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
    refine lessRG impl R hpre hS hr0 (by omega) _ fun S' hA => ?_
    subst hu
    exact lessC0 impl R hmz hpre hA hU z2.isLt hra hx15 hdf

/-- `DivPreGQ` (with the interface cost `cost ul vl + stkR H s.mem st`) survives writing the return address: the `hinv` of `ensLG` and of the row
`DivRowQ.correctness`. `DivPreGQ` states the location facts of the dividend `u` under `0 < ul` only: an empty `u` (a read of 0 bytes) has no apartness
from the return slot, so the empty / non-empty cases are split and `0 < ul` is given to the rewriting (a plain `omega` over the ~40 disjunctive facts of
the context is exponential for every side condition that is not a single disjunction). -/
theorem divpregq_setRet (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (cost : Nat → Nat → Nat) (z zl zc st z2 z2l z2c : BitVec 64)
    (u ul uc v vl vc : Nat) (p : Janus.Amd64.Program) (entry : Nat) (args : List W64) :
    Ensures.SetRetInv p entry args (fun s => ExpSlow.DivPreGQ R b H (cost ul vl + FvModexp.stkR H s.mem st.toNat) L 41512 112 z.toNat
      zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) := by
  intro s ret hs hret hp
  by_cases hu : ul = 0
  · subst hu
    janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpSlow.DivPreGQ, FvModexp.stkR, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet]
  · have hul : 0 < ul := Nat.pos_of_ne_zero hu
    janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpSlow.DivPreGQ, FvModexp.stkR, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hul, true_implies]

/-- **`nat.div`** (amd64) in expmc's empty-tolerant / results-apart form (`ExpSlow.DivHypLG`): premise
`DivLarge.HypG` and the live runtime contracts -/
theorem ensLG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc) :
    ExpSlow.DivHypLGQ impl R names 41512 112 (costQ dc) := by
  intro H b L zp zl zc st z2 z2l z2c u ul uc v vl vc
  rw [show ExpHyp.fnDiv = fn from rfl, show names = LibDiv.names from rfl, ← LibDiv.eq_only]
  refine Ensures.of_old (divpregq_setRet R H b L (costQ dc) zp zl zc st z2 z2l z2c u ul uc v vl vc _ _ _) ?_
  intro ret hret s hs hpre
  janus64_intro hs
  by_cases hu : ul = 0
  · exact Summary.returns (fullZ impl hap R hmk0 hmv0 hmz0 dc b L zp zl zc st z2 z2l z2c u ul uc v vl vc hu) hret
      (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
        h_a3, h_a4, h_a5, h_a6, hpre⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · exact Summary.returns (full impl hap R hmk0 hmv0 hmz0 dc hL b L zp zl zc st z2 z2l z2c u ul uc v vl vc) hret
      (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
        h_a3, h_a4, h_a5, h_a6, PreG.toPre hpre (by omega)⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- `ensLG` with `divLarge` discharged (`DivLarge.ensG`): premise `DrsHyp` and the live runtime contracts -/
theorem ensDLG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DivLarge.DrsHypQ impl R dc) :
    ExpSlow.DivHypLGQ impl R names 41512 112 (costQ dc) :=
  ensLG impl hap R hmk0 hmv0 hmz0 dc (DivLarge.ensG impl hap R hgr hmc hwb hmk0 hmv0 dc hD)

end FvModexp.Amd64.Q.NatDiv
