import FvModexp.Proofs.Arm64.Top.RunOkRow
import FvModexp.Proofs.Arm64.Exp.IExpSpec
import FvModexp.Proofs.Arm64.Exp.DivInst
import FvModexp.Proofs.Arm64.Nat.DivC

set_option autoImplicit false

/-!
# Row 1, arm64, success path with `(*Int).exp` and `nat.div` plugged in (agent top s20)

`correctness_okE` = `Run.correctness_ok` with the `ExpSpec` premise discharged by expmc's `IExp.ens` (`(*Int).exp` →
`nat.expNN` on the `stk == nil` path), whose `nat.div` premise (`ExpN.DHyps.div`) is in turn discharged by asm's closed
`NatDiv.ensCL` (StackBackL form, `nat.mul` discharged by divmc). The runtime contracts are all taken on
`Extracted.program.ofImpl impl` (Janus-pinned form) and moved to the library programs by `CodeIn`.

STILL PREMISES (each a callee proof not yet on main, or a cost bound):
* `hM : RunIface.ModSpec` — `(*Int).Mod` (divmc, not started on the `stk == nil` path);
* `hSl` / `hP2` / `hEv` — `nat.expNNSlow`, `nat.expNNPowerOfTwo`, `nat.expNNEven` (infra) with their name / depth facts;
* `hRem` — `nat.rem` (asm, in progress: `NatRem.RemHypNA`, waits for expmc's `NoAlias` amendment of `RemHyp`);
* `hneed` / `hbud` — the cost-function bounds of `IExp.ens` (functions of the four premises above, `ExpBudget`);
* the live runtime contracts (`makeslice`, `MakesliceZeroLive`, `memmove`, `MemmoveZeroLive`, `newobject`, `growslice`,
  `memclrNoHeapPointers`, `gcWriteBarrier2`, `sync.(*Pool).Get/Put` at `StkSh`) — Janus contracts; the two `…Zero…` are
  local copies of Janus PR #2 until the v0.3.1 re-pin.

`expSpec_of_X`: expmc's local `IExp.ExpSpecX` implies the final `RunIface.ExpSpec` (its extra pre facts `ExpX` are now
conjuncts of `ExpSpec`'s pre / `IntOK`'s cap bound; its extra post conjunct is dropped).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool Janus.Contracts.EqHashModel
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- expmc's local form `IExp.ExpSpecX` gives the final `RunIface.ExpSpec` (= expmc's `IExp.ExpSpecM`, whose last pre
conjunct `ModX` top folded into `ExpSpec`). -/
theorem expSpec_of_X {impl : List Segment} {R : RtInv} {stk above : Nat} (h : IExp.ExpSpecX impl R stk above) :
    RunIface.ExpSpec impl R stk above := IExp.ExpSpecX.toSpecM h

theorem libN_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibN.program.link impl) := by
  rw [LibN.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libNE_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibNE.program.link impl) := by
  rw [LibNE.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libExp_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibExp.program.link impl) := by
  rw [LibExp.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

theorem libFree_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibFree.program.link impl) := by
  rw [LibFree.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap _

/-- **Row 1, arm64, EIP-7823 success**, `(*Int).exp` and `nat.div` discharged (premises: module doc). -/
theorem correctness_okE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (hSl : NHyp.SlowHyp impl R nsS stkS 112 needS costS)
    (hnsS : ∀ x, nsS.contains x = true → LibN.names.contains x = true)
    (hn11S : nsS.contains Extracted.seg11.name = false) (hKS : stkS ≤ K + 1056)
    (hP2 : NHyp.P2Hyp impl R nsP stkP 112 needP costP)
    (hnsP : ∀ x, nsP.contains x = true → LibN.names.contains x = true)
    (hn11P : nsP.contains Extracted.seg11.name = false) (hKP : stkP ≤ K + 1056)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE) (hstkE : stkE ≤ K + 1056)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (hKD : 41504 ≤ K) (hK20 : K + 288 ≤ 2 ^ 20)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ ExpN.addN needS needE xl yl n ≤ 2 ^ 16 ∧ needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + costR 0 xl n + ExpN.addC costS costE 0 xl yl n + costP 0 xl yl lm +
        ExpOdd.OBud (NatDiv.cost DivRec.drsC) n xl yl 0) ≤ RunIface.ExpBudget (max (max xl yl) n) yl ∧
      24 + ExpN.NCost (NatDiv.cost DivRec.drsC) costR (ExpN.addC costS costE) costP xl yl n 0 lm ≤
        RunIface.ExpBudget (max (max xl yl) n) yl)
    (stkM aboveM : Nat) (hM : RunIface.ModSpecM impl R stkM aboveM)
    (hKs : K + 1632 ≤ stkM) (W : Nat) (hW : 624 + stkM ≤ W) (hab : aboveM ≤ 160) (ha1 : 48 ≤ aboveM)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
        RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
        RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') := by
  have hD : ExpN.DHyps impl R K (NatDiv.cost DivRec.drsC) needS needP costS costP NatDiv.names 41504 nsS stkS nsP
      stkP :=
    { mkN := MakesliceLiveContract.of_codeIn (libN_code impl hap) hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr,
      wb := hwb, div := NatDiv.ensCL impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub,
      hnsW4 := DivInst.ns_w4, hnsW2 := DivInst.ns_w2, hKD := hKD, slow := hSl, hnsS := hnsS, hn11S := hn11S,
      hKS := hKS, p2 := hP2, hnsP := hnsP, hn11P := hn11P, hKP := hKP }
  have hE : RunIface.ExpSpec impl R stkM aboveM := expSpec_of_X <|
    IExp.ens impl hap R hD hEv hstkE (fun L b => Summary.of_codeIn (libNE_code impl hap) (hget L b))
      (NewobjectLiveContract.of_codeIn (libNE_code impl hap) hno)
      (fun L b rs => Summary.of_codeIn (libFree_code impl hap) (hput L b rs)) hRem hnsR hn11R hKR
      (WbLiveContract.of_codeIn (libExp_code impl hap) hwb) hKs (by omega) hK20 (by omega) ha1 hneed hbud
  exact correctness_ok impl hap R hmk hmkz hmv hmz hno stkM aboveM hM hE W hW (by omega) hab (by omega) (by omega) b L
    c p len cp

end FvModexp.Arm64.Run
