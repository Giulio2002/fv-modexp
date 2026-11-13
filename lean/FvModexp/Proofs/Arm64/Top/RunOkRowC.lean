import FvModexp.Proofs.Arm64.Top.RunModC
import FvModexp.Proofs.Arm64.Top.RunOkRow
import FvModexp.Proofs.Arm64.ExpQ.IExpClBQ

set_option autoImplicit false

/-!
# Row 1, arm64, success path with EVERY machine-code callee proved (agent top s26)

`correctness_okC` = `Run.correctness_ok` (`ensOkLib`: Run's own code, `(*Int).Bytes` = `IntBytes.bytesSpec_at`) with
* `(*Int).Mod` (`hM`) = `modSpecM_C` (divmc's `IMod.ens` + `IMod.bud`, asm's `NatDiv.ensMC`);
* `(*Int).exp` (`hE`) = `expC` below = expmc's `IExp.ensClBQ` (ExpQ/IExpClBQ.lean): `(*Int).exp` with every callee
  proved and the CLOSED Q-form cost bound (`IExp.budClQC`), windows `KN = 70720`, `stkE = 72368`, `K = 71312`.

Premises: the Janus runtime contracts on `Extracted.program.ofImpl impl` only (BRIEF "TIGHT COSTS": `RunIface.ExpBudget` =
the factor-free `BudQ.ExpBudgetF`; the former `hbud : IExp.BudCl` premise is discharged, top s40).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open Janus.Contracts.EqHashModel
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run.Closed

set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it, every machine-code callee proved: expmc's `IExp.ensClBQ` (premises = the
Janus runtime contracts only). -/
theorem expC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {stk above : Nat} (hK : 72944 ≤ stk) (hab : 48 ≤ above) :
    RunIface.ExpSpec impl R stk above :=
  IExp.ensClBQ impl hap R hmk hgr hmc hmv hmz hno hwb hget hput (K := 71312) (KN := 70720) (stkE := 72368)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) hab

end FvModexp.Arm64.Run.Closed

namespace FvModexp.Arm64.Run

set_option maxHeartbeats 64000000 in
/-- **Row 1, arm64, EIP-7823 success**, every machine-code callee proved (`(*Int).Mod`, `(*Int).exp` with the whole
`nat` chain, `(*Int).Bytes`); premises: the Janus runtime contracts only. -/
theorem correctness_okC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (W : Nat) (hW : 624 + 72944 ≤ W) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
        RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
        RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') :=
  correctness_ok impl hap R hmk hmkz hmv hmz hno 72944 112
    (modSpecM_C impl hap R hgr hmc hwb hmk hmv hmz hno hget hput hwb4 (by decide) (by decide))
    (Closed.expC impl hap R hmk hgr hmc hmv hmz hno hwb hget hput (Nat.le_refl _) (by decide))
    W hW (by omega) (by decide) (by decide) (by decide) b L c p len cp

end FvModexp.Arm64.Run
