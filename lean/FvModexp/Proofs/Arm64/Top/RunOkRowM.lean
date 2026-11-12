import FvModexp.Proofs.Arm64.Top.RunOkRowEv
import FvModexp.Proofs.Arm64.Nat.DivMC
import FvModexp.Proofs.Arm64.Int.ModBud

set_option autoImplicit false

/-!
# Row 1, arm64, success path: `nat.div` of `(*Int).Mod` (asm's `NatDiv.ensMC`) plugged in (agent top s23)

`correctness_okM` = `Run.correctness_okEv` with its `IMod.DivHypM` premise discharged by asm's `NatDiv.ensMC`
(`nil.div(nil, u, u, v)`, every callee proved), `nsD = LibDiv.names`, `stkD = 41504`, `aboveD = 112`, and the Mod budget
`hbudM` discharged by divmc's `IMod.bud` (Arm64/Int/ModBud.lean) — so `(*Int).Mod` is fully discharged (as divmc's `IMod.ensC`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool Janus.Contracts.EqHashModel
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- `(*Int).Mod` with `nat.div` and the budget discharged (= divmc's `IMod.ensC`, in the `ModSpecM` form) -/
theorem modSpecM_C (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {stkM aboveM : Nat} (hstkD : 41504 + 304 ≤ stkM) (hab : 32 ≤ aboveM) :
    RunIface.ModSpecM impl R stkM aboveM :=
  modSpecM_ens impl hap R hwb4 (NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput)
    NatDiv.libDiv_sub_mod NatDiv.libDiv_noQuoRem (by decide) IMod.bud hstkD (by omega) hab

set_option maxHeartbeats 64000000 in
/-- **Row 1, arm64, EIP-7823 success**, `(*Int).exp`, `nat.div` (both calls), `nat.expNNEven` and `(*Int).Mod` discharged (premises: module doc). -/
theorem correctness_okM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
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
    (stkM aboveM : Nat) (hstkD : 41504 + 304 ≤ stkM) (h4448 : 4448 ≤ stkM)
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
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  correctness_okEv (hDM := NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput)
    (hnsD := NatDiv.libDiv_sub_mod) (hnsQ := NatDiv.libDiv_noQuoRem) (habD := by decide)
    impl hap R hmk hmkz hmv hmz hno hgr hmc hwb hget hput hwb4 hSl hnsS hn11S hKS hP2 hnsP hn11P hKP hRem hnsR hn11R
    hKR hKN hk1 hk2 hk3 hstkE hK20 hRm hSm hPm hNB hNC hneed hbud IMod.bud stkM aboveM hstkD h4448 hKs W hW hab ha1 b L
    c p len cp

end FvModexp.Arm64.Run
