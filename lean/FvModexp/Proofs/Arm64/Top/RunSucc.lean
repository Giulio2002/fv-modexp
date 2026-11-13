import FvModexp.Proofs.Arm64.Top.RunOkRowC
import FvModexp.Proofs.Arm64.Int.ModRowW
import FvModexp.Proofs.Arm64.Top.RunSuccW2

set_option autoImplicit false

/-!
# Row 1, arm64, success half: `(*bigModExp).Run` on call data that passes EIP-7823 (agent top s27)

`correctness`: for every input slice whose length headers pass `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns `(out, nil)` with `out = compute data (parseLengths data)` (EthLib), keeping the Go ABI and
the memory frame (`Spec.RunArm64`: `EnvW`, `Input`, `OkReqs`, `Globals`, `NatOne`, `StackPool`, `okBudget`, `OkRet`,
`FrameW`). Every machine-code callee is proved (`Run.correctness_okC`: `(*Int).Mod`, `(*Int).exp` with the whole `nat`
chain and the closed Q-form cost bound (expmc's `IExp.ensClBQ`), `(*Int).Bytes`); the premises are the Janus runtime
contracts on `Extracted.program.ofImpl impl` only. The budget is the factor-free one (BRIEF "TIGHT COSTS", top s40:
`RunIface.ExpBudget = BudQ.ExpBudgetF`, `okBudget` without the former `2^32` slack).

`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy allocator `toyR [] (fun _ _ => True)`, heap `2^22`),
budget `bW = 0x300000`, window `0x20000`, empty live set, and a REAL exponentiation: `Run(c, p, 99, 99)` on the call data
with lengths `1, 1, 1`, `B = 3`, `E = 5`, `M = 7` (`Run.WitnessOk.s2`, Top/RunSuccW2.lean), output `[5]` (`compute2`); the
budget fits (`budget2`, `decide`); one call-site state per runtime contract (`AsmWit` / `Sites` / `RunOkRow` site lemmas).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.RunSucc

/-- the release gate (BRIEF "TIGHT COSTS"): `ExpBudget` = the factor-free `BudQ.ExpBudgetF` (definitionally), so the
largest `(*Int).exp` budget of the spec range (128-word operands, 128-word exponent) is at most `2^35` bytes (32 GiB) -/
theorem expBudget_eq (w yW : Nat) : RunIface.ExpBudget w yW = BudQ.ExpBudgetF w yW := rfl

theorem expBudget_gate : RunIface.ExpBudget 128 128 ≤ 2 ^ 35 := BudQ.gate

/-- **Row 1, arm64, EIP-7823 success**: `Run` returns `(compute data (parseLengths data), nil)`. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (S : PoolShape)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT S)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT S)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4)
    (W : Nat) (hW : 624 + 72944 ≤ W) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => S = StkSh ∧ RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
        RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
        RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') := by
  -- the Pool shape is a row binder fixed by the precondition (Janus's PoolShape row pattern; audit, v0.3.1)
  intro ret hret s hs ⟨hS, hpre⟩
  subst hS
  exact Run.okC impl hap R hmk hmkz hmv hmz hno hgr hmc hwb hget hput hwb4 W hW b L c p len cp ret
    hret s hs hpre

end FvModexp.Arm64.RunSucc

open Janus.Contracts.Toy Janus.Contracts.LiveSat

namespace FvModexp.Arm64.RunSucc.Witness

open FvModexp.Arm64.Run.Witness (implAt hap R tys0 ok hret ret)
open FvModexp.Arm64.Run.WitnessOk (s2 c2 p2 WW bW setup2 pre2 sMkz site_mkz sMz site_mz compute2)
open FvModexp.Arm64.AsmWit (callS callS5 callP OA OB mkSite mvSite noSite grSite clSite wbSite getSite putSite)

set_option maxRecDepth 100000
/-- Every hypothesis of `correctness` (the eleven runtime contracts, the window) and every conjunct of its
precondition hold together, with one call-site state per contract, and the call returns: the shared witness runtime,
budget `bW`, window `WW`, empty live set, `Run(c, p, 99, 99)` on lengths `1, 1, 1`, `3^5 mod 7` (output `[5]`). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (c p len cp : BitVec 64) (ret : Nat) (s : State) (W : Nat),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MakesliceZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh ∧
    PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    624 + 72944 ≤ W ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp] s ∧
    StkSh = StkSh ∧ RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
    RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
    RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
    RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
    LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧
    compute (bytesAt s.mem p.toNat len.toNat) (parseLengths (bytesAt s.mem p.toNat len.toNat)) = ⟨#[5]⟩ ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      ((MakeslicePre 4096 s_c ∧ StackRoom s_c 4096 3 ∧
        LiveAt R (Extracted.program.contractAddr "runtime.makeslice") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
          (s_c.regs 2).toNat] L b 0 (s_c.regs 28).toNat s_c.mem (calleeStack s_c 4096 3)) ∧
        typSize s_c.mem (s_c.regs 0).toNat * (s_c.regs 2).toNat = 0 ∧
        Outside (s_c.regs 0).toNat 16 (calleeStack s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      ((s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
        LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
          (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  Run.WitnessC.nonvacuous

end FvModexp.Arm64.RunSucc.Witness
