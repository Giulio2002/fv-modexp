import FvModexp.Proofs.Amd64.Top.RunSuccWit

set_option autoImplicit false

/-!
# Row 1, amd64, success half: `(*bigModExp).Run` on call data that passes EIP-7823 — STAGING (agent top s34, s49)

Twin of `Arm64/Top/RunSucc.lean`, final statement shape: the arm64 row's pre/post with `Spec.RunAmd64`, the Pool shape
`S` a binder fixed by the precondition (`S = Spec.StkShape`, Janus's PoolShape row pattern), plus the amd64-only entry
facts `Spec.RunAmd64.CpuOne` (`hasADX` readable, `natOne`'s word apart from the threshold globals), which amd64
`(*Int).Mod` / `(*Int).exp` need (`ModSpecA` / `ExpSpecA`, coordinator decisions 2026-11-14).
* `(*Int).Mod`: CLOSED (`Run.Closed.modA`: divmc's `IMod.mod_ensD` + asm's `Q.NatDiv.ensMC` + `Q.BudM.bud`).
* `(*Int).exp`: still the PREMISE `hE : RunIface.ExpSpecA impl R stkM aboveM` (= expmc's `IExp.ExpSpecA` by definition),
  until the closed amd64 `(*Int).exp` lands (expmc: `IExp.ens` with the closed callee instances; open: `DHyps.slow`,
  amd64 `nat.expNNSlow`). Then `hE` is replaced and `Witness.nonvacuous` = `Run.WitnessA.nonvacuous_of` (Top/RunSuccWit; 3^5 mod 7) is added,
stated inline (literal names only).
Not a release row yet (`hE` is not a Janus-pinned contract).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.RunSucc

/-- the Spec copies (Spec/Pool, Spec/WitSitesAmd64) are the proof-side defs -/
theorem stkShape_eq : StkShape = StkSh := rfl
theorem stkT_eq : WitSitesAmd64.stkT = Free.stkT := rfl

set_option maxHeartbeats 64000000 in
/-- **Row 1, amd64, EIP-7823 success** (staging): `Run` returns `(compute data (parseLengths data), nil)`, every
machine-code callee proved except `(*Int).exp` (`hE`). -/
theorem correctness (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (S : PoolShape)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R WitSitesAmd64.stkT S)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R WitSitesAmd64.stkT S)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
      4096 R 4)
    (stkM aboveM : Nat) (hE : RunIface.ExpSpecA impl R stkM aboveM)
    (W : Nat) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (hk : 41800 ≤ stkM) (ha : 16 ≤ aboveM)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => S = StkShape ∧ RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  Run.okA impl hap R hmk hmkz hmv hmz hno hgr hmc hwb S hget hput hwb4 stkM aboveM hE W hW hW1 hab hk ha b L c p len cp

end FvModexp.Amd64.RunSucc
