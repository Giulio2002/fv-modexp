import FvModexp.Proofs.Amd64.NatQ.DivMGetK
import FvModexp.Proofs.Amd64.NatQ.DivMOneA
import FvModexp.Proofs.Amd64.NatQ.DivMOneC
import FvModexp.Proofs.Amd64.NatQ.DivMOneTB
import FvModexp.Proofs.Amd64.NatQ.DivMOneTC
import FvModexp.Proofs.Amd64.NatQ.DivMLessA
import FvModexp.Proofs.Amd64.NatQ.DivMLess
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-! (twin of Arm64/NatQ/DivMFull.lean, TIGHT COSTS, top s43)
# `nil.div(nil, u, u, v)` (go-bigmodexpfix natdiv.go:518, `stk == nil`, `z = nil`, `z2 = u`), amd64 — the composition

As `(*Int).QuoRem` calls it from `(*Int).Mod` (`IMod.DivHypM`, Amd64/Int/ModDivHyp.lean).
`len v = 1`: `one1M` → `one2M` (`divW`) → `oneAM | oneBM | oneCM` (`setWord`); `len v ≥ 2`: `two1M` → `two2M` (`cmp`) →
`u < v`: `lessRM` (`z2 = u` has `cap ≥ len u`) → `lessSM` (self-copy skipped); `u ≥ v`: `bigM` (`getStack()` =
`Pool.Get` / `newobject`, defer record, `divLarge`, deferred `stk.free()` = `Pool.Put`).
`ensML`: the `Ensures` = `IMod.DivHypM impl R LibDiv.names 41512 112 (costMQ dc)`; premises `DivLarge.HypG` and the live
runtime contracts on `Extracted.program.ofImpl impl` (`Pool.Put` moved into `LibDivFree` by `libDivFree_code`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv

theorem libDivFree_code (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 (Extracted.program.ofImpl impl) (LibDivFree.program.link impl) := by
  rw [LibDivFree.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDivFree.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fullM (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput0 : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat) :
    Summary (LibDiv.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = 0#64 ∧ s.regs 3 = 0#64 ∧ s.regs 1 = 0#64 ∧ s.regs 7 = 0#64 ∧ s.regs 6 = u ∧ s.regs 8 = ul ∧
        s.regs 9 = uc ∧ PreM R b dc L u.toNat ul.toNat uc.toNat v vl vc s)
      (fun s s' => RQM R b dc L u.toNat ul.toNat uc.toNat v vl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hc3 := codeIn_lib impl hap
  have hmk := MakesliceLiveContract64.of_codeIn hc3 hmk0
  have hno := NewobjectLiveContract64.of_codeIn hc3 hno0
  have hget : Janus.Contracts.PoolAmd64.PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh := fun L b => Summary.of_codeIn64 hc3 (hget0 L b)
  have hput : Janus.Contracts.PoolAmd64.PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh := fun L b rs => Summary.of_codeIn64 (libDivFree_code impl hap) (hput0 L b rs)
  have hp := hpre.f
  have hv0 := hp.v0
  by_cases hv1 : vl = 1
  · subst hv1
    refine one1M impl R b dc L 0#64 0#64 0#64 0#64 u ul uc u.toNat ul.toNat uc.toNat v vc s hpc hx15 hdf h0 h3 h1 h7
      h6 h8 h9 hp _ fun X hX => one2M impl hap R hmk0 hmv0 hmz0 b dc L u.toNat ul.toNat uc.toNat v vc s hp X hX _
        fun q ql qc L' b' T hW => ?_
    by_cases hr0 : natVal s.mem u.toNat ul.toNat % natVal s.mem v 1 = 0
    · exact oneAM impl R hp hW hr0 hra hx15 hdf
    · rcases Nat.eq_zero_or_pos uc.toNat with hz | hz
      · rw [hz] at hp hW ⊢
        exact oneCM impl R hmk hp hW hr0 hra hx15 hdf
      · exact oneBM impl R hp hW hr0 hz hra hx15 hdf
  · have hv2 : 2 ≤ vl := by omega
    refine two1M impl R b dc L 0#64 0#64 0#64 0#64 u ul uc u.toNat ul.toNat uc.toNat v vl vc s hpc hx15 hdf h0 h3 h1
      h7 h6 h8 h9 hv2 hp _ fun X hX => two2M impl hap R b dc L 0#64 0#64 0#64 0#64 u ul uc u.toNat ul.toNat uc.toNat
        v vl vc s hp X hX _ fun S hS => ?_
    rcases Nat.lt_or_ge (natVal s.mem u.toNat ul.toNat) (natVal s.mem v vl) with hU | hU
    · have hr0 : S.regs 0 = 18446744073709551615#64 := by rw [hS.r0]; exact cmp_lt hp.un hU
      exact lessRM impl R hp hS hr0 hp.ulc _ fun S' hA => lessSM impl R hp hA hU hra hx15 hdf
    · obtain ⟨c, hc, hr0⟩ := cmp_ge hp.vn hU
      rw [← hS.r0] at hr0
      exact bigM impl hap R dc hL hget hput hno hp hU hv2 u.isLt hra hx15 hdf hS c hc hr0

theorem divprem_setRet_pp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul.toNat) (hg1 : 0 < uc.toNat)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IMod.DivPreM, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem divprem_setRet_pn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul.toNat) (hg1 : ¬ 0 < uc.toNat)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IMod.DivPreM, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem divprem_setRet_p (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul.toNat)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  by_cases hg1 : 0 < uc.toNat
  · exact divprem_setRet_pp R b cost L u ul uc v vl vc  s ret hs hret hg0 hg1 hp
  · exact divprem_setRet_pn R b cost L u ul uc v vl vc  s ret hs hret hg0 hg1 hp

theorem divprem_setRet_np (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul.toNat = 0) (hg1 : 0 < uc.toNat)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IMod.DivPreM, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem divprem_setRet_nn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul.toNat = 0) (hg1 : ¬ 0 < uc.toNat)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IMod.DivPreM, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem divprem_setRet_n (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul.toNat = 0)
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  by_cases hg1 : 0 < uc.toNat
  · exact divprem_setRet_np R b cost L u ul uc v vl vc  s ret hs hret hg0 hg1 hp
  · exact divprem_setRet_nn R b cost L u ul uc v vl vc  s ret hs hret hg0 hg1 hp

theorem divprem_setRet (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) 
    (hp : FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :
    FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc (s.setRet ret) := by
  by_cases hg0 : 0 < ul.toNat
  · exact divprem_setRet_p R b cost L u ul uc v vl vc  s ret hs hret  hg0 hp
  · exact divprem_setRet_n R b cost L u ul uc v vl vc  s ret hs hret  (Nat.eq_zero_of_not_pos hg0) hp

/-- `DivPreM` at `QuoRem`'s call survives writing the return address (the `hinv` of `ensML`): the empty dividend (`ul = 0`) and `0 < uc` are case-split,
one declaration per case (`divprem_setRet_<ul><uc>`). -/
theorem divprem_inv (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat)
    (p : Janus.Amd64.Program) (entry : Nat) (args : List W64) :
    Ensures.SetRetInv p entry args (fun s => FvModexp.Amd64.IMod.DivPreM R b cost L 41512 112 u.toNat ul.toNat uc.toNat v vl vc s) :=
  fun s ret hs hret hp => divprem_setRet R b cost L u ul uc v vl vc s ret hs hret hp

/-- **`nat.div`** (amd64) as `(*Int).QuoRem` calls it from `(*Int).Mod`: `q, r = nil.div(nil, u, u, v)` (`stk == nil`,
`z2 = u`; `v ≠ 0`, `u`, `v` normalised, `len ≤ 2^9`) returns `r = U mod V` normalised, in `u`'s array or a fresh one;
writes only `u`'s array, the runtime's memory and the window; no panic, no fault (`IMod.DivHypM`, TIGHT COSTS budget
`costMQ dc`). Premises: `DivLarge.HypG` and the live runtime contracts. -/
theorem ensML (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput0 : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc) :
    IMod.DivHypM impl R LibDiv.names 41512 112 (costMQ dc) := by
  intro b L u ul uc v vl vc
  rw [show ExpHyp.fnDiv = fn from rfl, ← LibDiv.eq_only]
  refine Ensures.of_old (divprem_inv R b (costMQ dc) L u ul uc v vl vc _ _ _) ?_
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (fullM impl hap R hmk0 hmv0 hmz0 hno0 hget0 hput0 dc hL b L u ul uc v vl vc) hret
    (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2,
      h_a3, h_a4, h_a5, h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

end FvModexp.Amd64.Q.NatDiv
