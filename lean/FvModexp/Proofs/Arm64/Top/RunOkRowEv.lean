import FvModexp.Proofs.Arm64.Top.RunOkRowE
import FvModexp.Proofs.Arm64.Exp.EvInst
import FvModexp.Proofs.Arm64.Exp.NFun
import FvModexp.Proofs.Arm64.Exp.NCap

set_option autoImplicit false

/-!
# Row 1, arm64, success path with `(*Int).exp`, `nat.div` AND `nat.expNNEven` plugged in (agent top s21)

`correctness_okEv` = `Run.correctness_okE` with its `hEv : ExpEven.EvenSum …` premise discharged by infra's
`ExpEven.fullI` (`nat.expNNEven` with every callee summary proved), whose own premise on the inner `nat.expNN` calls
(`EvenHyp.ExpNNHypNE1`, window `KN`) is expmc's `ExpN.ens_noEven` (via `ExpNNHypNE.toNE1`) on a second `DHyps`
instance at `KN` (division = asm's `NatDiv.ensCL`, the same slow / power-of-two / rem premises).

The inner window `KN` sits below the outer `K` (`KN + 1648 ≤ stkE ≤ K + 1056`), so the stack-depth premises of the
slow / power-of-two / rem callees are stated once, at `KN`, and give the ones at `K`.

STILL PREMISES (see NOTES-conventions "[top s21] arm64 success-row premise list"): `ModSpec`, `SlowHyp`, `P2Hyp`,
`RemHyp`, the cost bounds `hneed`/`hbud`, the monotonicity facts of `fullI` (`hRm hSm hPm hNB hNC`), and the Janus
runtime contracts (two of them local PR #2 copies until the v0.3.1 re-pin).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool Janus.Contracts.EqHashModel
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

set_option maxHeartbeats 64000000 in
/-- **Row 1, arm64, EIP-7823 success**, `(*Int).exp`, `nat.div` and `nat.expNNEven` discharged (premises: module doc). -/
theorem correctness_okEv (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    {K KN : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (hSl : NHyp.SlowHyp impl R nsS stkS 112 needS costS)
    (hnsS : ∀ x, nsS.contains x = true → LibN.names.contains x = true)
    (hn11S : nsS.contains Extracted.seg11.name = false) (hKS : stkS ≤ KN + 1056)
    (hP2 : NHyp.P2Hyp impl R nsP stkP 112 needP costP)
    (hnsP : ∀ x, nsP.contains x = true → LibN.names.contains x = true)
    (hn11P : nsP.contains Extracted.seg11.name = false) (hKP : stkP ≤ KN + 1056)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ KN + 1056)
    (hKN : 41504 ≤ KN) {stkE : Nat} (hk1 : 71168 ≤ stkE) (hk2 : stkE ≤ 2 ^ 20 + 336) (hk3 : KN + 1648 ≤ stkE)
    (hstkE : stkE ≤ K + 1056) (hK20 : K + 288 ≤ 2 ^ 20)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpEven.NBudE (NatDiv.cost DivRec.drsC) costR costS costP x y a l k ≤
        ExpEven.NBudE (NatDiv.cost DivRec.drsC) costR costS costP x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost (NatDiv.cost DivRec.drsC) costR costS costP x y a l k ≤
        ExpN.NCost (NatDiv.cost DivRec.drsC) costR costS costP x y a' l' k')
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ ExpN.addN needS (ExpEven.needE needR needS needP) xl yl n ≤ 2 ^ 16 ∧
        needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + costR 0 xl n +
        ExpN.addC costS (ExpEven.costE (NatDiv.cost DivRec.drsC) costR costS costP sqrC mulC mulC) 0 xl yl n +
        costP 0 xl yl lm + ExpOdd.OBud (NatDiv.cost DivRec.drsC) n xl yl 0) ≤ RunIface.ExpBudget (max (max xl yl) n) yl ∧
      24 + ExpN.NCost (NatDiv.cost DivRec.drsC) costR
        (ExpN.addC costS (ExpEven.costE (NatDiv.cost DivRec.drsC) costR costS costP sqrC mulC mulC)) costP xl yl n 0 lm ≤
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
  have hDN : ExpN.DHyps impl R KN (NatDiv.cost DivRec.drsC) needS needP costS costP NatDiv.names 41504 nsS stkS nsP
      stkP :=
    { mkN := MakesliceLiveContract.of_codeIn (libN_code impl hap) hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr,
      wb := hwb, div := NatDiv.ensCL impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub,
      hnsW4 := DivInst.ns_w4, hnsW2 := DivInst.ns_w2, hKD := hKN, slow := hSl, hnsS := hnsS, hn11S := hn11S,
      hKS := hKS, p2 := hP2, hnsP := hnsP, hn11P := hn11P, hKP := hKP }
  have hNE : EvenHyp.ExpNNHypNE impl R KN (NatDiv.cost DivRec.drsC) needR costR needS needP costS costP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem hnsR hn11R hKR b L zp zl zc st xp xl xc yp yl yc mp n mc slow
  have hEv := ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by omega) (by omega)
    hRm hSm hPm hNB hNC hk1 hk2 hk3
  exact correctness_okE impl hap R hmk hmkz hmv hmz hno hgr hmc hwb hget hput hSl hnsS hn11S (by omega) hP2 hnsP hn11P
    (by omega) hEv hstkE hRem hnsR hn11R (by omega) (by omega) hK20 hneed hbud stkM aboveM hM hKs W hW hab ha1 b L
    c p len cp

end FvModexp.Arm64.Run
