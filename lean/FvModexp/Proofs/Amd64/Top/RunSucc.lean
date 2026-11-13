import FvModexp.Proofs.Amd64.Top.RunOkRow

set_option autoImplicit false

/-!
# Row 1, amd64, success half: `(*bigModExp).Run` on call data that passes EIP-7823 — SKELETON (agent top s34)

Twin of `Arm64/Top/RunSucc.lean`. `correctness` has the final statement (the arm64 row's pre/post with `Spec.RunAmd64`);
the two plug points are still PREMISES, as in `Run.correctness_ok`:
* `hM : RunIface.ModSpecM impl R stkM aboveM` — amd64 `(*Int).Mod` (to come: an amd64 `modSpecM_C` from amd64 `IMod`
  + `NatDiv.ens`/`ensD` (Amd64/Nat/Div.lean, top s34) + asm's amd64 `nat.rem`);
* `hE : RunIface.ExpSpec impl R stkM aboveM` — amd64 `(*Int).exp` (to come: amd64 `IExp.ensCl`).
When both land, they are replaced by their `Closed` proofs from the Janus runtime contracts (adding `growslice`,
`memclrNoHeapPointers`, `gcWriteBarrier2/4`, `sync.(*Pool).Get/Put` with the row's `PoolShape` binder fixed by the
precondition — arm64 RunSucc's pattern) and the witness `RunSucc.Witness.nonvacuous` (3^5 mod 7, BRIEF "TIGHT COSTS").
Not a release row yet (its premises hM/hE are not Janus-pinned contracts).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.RunSucc

/-- **Row 1, amd64, EIP-7823 success** (skeleton): `Run` returns `(compute data (parseLengths data), nil)`, given amd64
`(*Int).Mod` (`hM`) and `(*Int).exp` (`hE`) summaries. -/
theorem correctness (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (stkM aboveM : Nat) (hM : RunIface.ModSpecM impl R stkM aboveM) (hE : RunIface.ExpSpec impl R stkM aboveM)
    (W : Nat) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (hk1 : 4160 ≤ stkM) (ha1 : 16 ≤ aboveM)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  Run.correctness_ok impl hap R hmk hmkz hmv hmz hno stkM aboveM hM hE W hW hW1 hab hk1 ha1 b L c p len cp

end FvModexp.Amd64.RunSucc
