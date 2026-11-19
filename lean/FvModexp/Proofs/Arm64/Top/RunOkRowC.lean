import FvModexp.Proofs.Arm64.Top.RunModC
import FvModexp.Proofs.Arm64.Top.RunOkRow
import FvModexp.Proofs.Arm64.ExpQ.IExpClBQ
import FvModexp.Proofs.Arm64.Int.ModRowW
import FvModexp.Proofs.Arm64.Top.RunSuccW2

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
theorem okC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (RunIface.ModSpecL.ofM (modSpecM_C impl hap R hgr hmc hwb hmk hmv hmz hno hget hput hwb4 (by decide) (by decide)))
    (RunIface.ExpSpecL.of (Closed.expC impl hap R hmk hgr hmc hmv hmz hno hwb hget hput (Nat.le_refl _) (by decide)))
    W hW (by omega) (by decide) (by decide) (by decide) b L c p len cp

set_option maxHeartbeats 64000000 in
/-- **Row 1, arm64, EIP-7823 success** (`okC` on Janus's PoolShape row pattern: the Pool shape `S` is a binder, fixed to
`StkSh` by the precondition's first conjunct — audit, v0.3.1). `RunSucc.correctness` is this theorem. -/
theorem correctness_okC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
  janus_ensures_old [FvModexp.Spec.RunArm64.EnvW, FvModexp.Spec.RunArm64.Input, FvModexp.Spec.OsakaReceiver, FvModexp.Spec.RunArm64.Globals, FvModexp.Spec.RunArm64.windowW, FvModexp.Spec.RunArm64.NatOne, FvModexp.Spec.RunArm64.StackPool, FvModexp.Spec.bytesAt, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Spec.RunArm64.window, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.RunIface.wbA, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Arm64.IExp.pA, Janus.Spec.Pool.newOffset, FvModexp.Spec.byteOf]
  -- the Pool shape is a row binder fixed by the precondition (Janus's PoolShape row pattern; audit, v0.3.1)
  intro ret hret s hs ⟨hS, hpre⟩
  subst hS
  exact (okC impl hap R hmk hmkz hmv hmz hno hgr hmc hwb hget hput hwb4 W hW b L c p len cp).toOld ret
    hret s hs hpre

end FvModexp.Arm64.Run

open Janus.Contracts.Toy Janus.Contracts.LiveSat

namespace FvModexp.Arm64.Run.WitnessC

open FvModexp.Arm64.Run.Witness (implAt hap R tys0 ok hret ret)
open FvModexp.Arm64.Run.WitnessOk (s2 c2 p2 WW bW setup2 pre2 sMkz site_mkz sMz site_mz compute2)
open FvModexp.Arm64.AsmWit (callS callS5 callP OA OB mkSite mvSite noSite grSite clSite wbSite getSite putSite)

set_option maxRecDepth 100000

/-- The runtime models of every contract `correctness` assumes, on the shared witness runtime. -/
theorem m_mk : MakesliceLiveContract (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.makeslice")
    4096 R := by rw [WStubs.addr_mk]; exact WStubs.mk [] tys0 ok
theorem m_mkz : MakesliceZeroLive (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.makeslice")
    4096 R := by rw [WStubs.addr_mk]; exact WStubs.mkz [] tys0 ok
theorem m_mv : MemmoveLive (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.memmove") 4096 R := by
  rw [WStubs.addr_mv]; exact WStubs.mv R
theorem m_mvz : MemmoveZeroLive (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.memmove")
    4096 R := by rw [WStubs.addr_mv]; exact WStubs.mvz R
theorem m_no : NewobjectLiveContract (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.newobject")
    4096 R := by rw [WStubs.addr_no]; exact WStubs.no [] tys0 ok
theorem m_gr : GrowsliceLiveContract (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.growslice")
    4096 R := by rw [WStubs.addr_gr]; exact WStubs.gr [] tys0 ok
theorem m_cl : MemclrNoHeapPointersLive (Extracted.program.ofImpl implAt)
    (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R := by rw [WStubs.addr_cl]; exact WStubs.cl R
theorem m_wb2 : WbLiveContract (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
    4096 R 2 := by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] tys0 ok
theorem m_wb4 : WbLiveContract (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
    4096 R 4 := by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] tys0 ok
theorem m_get : PoolGetLive (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
    Free.stkT StkSh := by rw [WStubs.addr_get]; exact WStubs.get [] ok _ _
theorem m_put : PoolPutLive (Extracted.program.ofImpl implAt) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
    Free.stkT StkSh := by rw [WStubs.addr_put]; exact WStubs.put [] tys0 ok _ _

/-- The cost bound at the witness: lengths `1, 1, 1` fit the toy budget `bW = 0x300000` (heap `2^22`). -/
theorem budget2 : RunArm64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW := by
  decide +kernel

/-- The returning run at the witness call. -/
theorem returnsC :
    Returns ((Extracted.program.link implAt).withExit ret) (s2.setRet ret) fun s' =>
      ABIReturn (s2.setRet ret) s' ∧ (RunArm64.OkRet (bytesAt (s2.setRet ret).mem p2.toNat (99 : BitVec 64).toNat) s' ∧
        RunArm64.FrameW R bW (RunArm64.okBudget (parseLengths (bytesAt (s2.setRet ret).mem p2.toNat (99 : BitVec 64).toNat)))
          [] WW (s2.setRet ret) s') :=
  (Run.correctness_okC implAt hap R m_mk m_mkz m_mv m_mvz m_no m_gr m_cl m_wb2 StkSh m_get m_put m_wb4 WW (by decide) bW []
    c2 p2 99 99) s2 setup2 ⟨rfl, (pre2 budget2)⟩ ret hret

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
    CallSetup0 (segAddr Extracted.program RunArm64.fn) [c, p, len, cp] s ∧
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
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ (RunArm64.OkRet (bytesAt (s.setRet ret).mem p.toNat len.toNat) s' ∧
        RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt (s.setRet ret).mem p.toNat len.toNat))) L W (s.setRet ret) s') :=
  ⟨implAt, R, bW, [], c2, p2, 99, 99, ret, s2, WW, hap, m_mk, m_mkz, m_mv, m_mvz, m_no, m_gr, m_cl, m_wb2, m_get, m_put,
    m_wb4, by decide, hret, setup2, rfl,
    (pre2 budget2).1, (pre2 budget2).2.1, (pre2 budget2).2.2.1, (pre2 budget2).2.2.2.1, (pre2 budget2).2.2.2.2.1, (pre2 budget2).2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.2.1,
    (pre2 budget2).2.2.2.2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.2.2.2, compute2,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact AsmWit.site_mk _⟩,
    ⟨[], 0x1000, sMkz, by rw [WStubs.addr_mk]; rfl, by rw [WStubs.addr_mk]; exact site_mkz⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact AsmWit.site_mv _⟩,
    ⟨[], 0x1000, sMz, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mz⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact AsmWit.site_no _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact AsmWit.site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact AsmWit.site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl,
      by rw [WStubs.addr_wb2]; exact AsmWit.site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact AsmWit.site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact AsmWit.site_put _⟩,
    ⟨[], 0x1000, callS WStubs.wb4A 0 0 0, by rw [WStubs.addr_wb4]; rfl,
      by rw [WStubs.addr_wb4]; exact AsmWit.site_wb _ _⟩,
    returnsC⟩

end FvModexp.Arm64.Run.WitnessC
