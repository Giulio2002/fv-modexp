import FvModexp.Proofs.Amd64.Top.RunModA
import FvModexp.Proofs.Amd64.Exp.IExpCl
import FvModexp.Proofs.Amd64.Top.RunSuccW2
import FvModexp.Proofs.Amd64.Int.ModRowW
import FvModexp.Proofs.Amd64.Witness.StubsGrow
import FvModexp.Spec.WitSitesAmd64

set_option autoImplicit false

/-!
# Row 1, amd64, success half: `Run` with `(*Int).Mod` closed, and its witness — STAGING for the exp plug-in (agent top s50)

Twin of `Arm64/Top/RunOkRowC.lean`.
* `Run.okA`: `Run.correctness_ok` with `(*Int).Mod` = `Run.Closed.modA` (closed), `(*Int).exp` still the premise
  `hE : RunIface.ExpSpecA impl R stkM aboveM` (expmc's `IExp.ExpSpecA`, by definition).
* `Run.WitnessA`: every piece of the row-1 success witness at the shared amd64 witness runtime (`WStubs`, `AsmWit.R`):
  the eleven runtime-contract models, one call-site state per contract (`Spec.WitSitesAmd64` copies, `rfl`), the call
  `Run(c, p, 99, 99)` on lengths `1, 1, 1`, `3^5 mod 7` (`RunSuccW2.s2`, with `CpuOne`), the cost bound, and
  `nonvacuous_of`: the full witness statement given `hE` AT THE WITNESS RUNTIME. When the closed amd64 `(*Int).exp`
  lands, `hE` is discharged there and `RunSucc.Witness.nonvacuous` is `nonvacuous_of (closed exp)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

set_option maxHeartbeats 64000000 in
/-- **Row 1, amd64, EIP-7823 success**, `(*Int).Mod` closed, `(*Int).exp` = `hE`; the Pool shape `S` is a binder fixed
by the precondition (Janus's PoolShape row pattern). -/
theorem okA (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') := by
  intro ret hret s hs ⟨hS, hpre⟩
  subst hS
  exact correctness_ok impl hap R hmk hmkz hmv hmz hno stkM aboveM
    (RunIface.ModSpecA.mono (Closed.modA impl hap R hmk hmv hmz hno hgr hmc hwb hget hput hwb4) hk ha) hE
    W hW hW1 hab (by omega) (by omega) b L c p len cp ret hret s hs hpre

namespace Closed

/-- **`(*Int).exp`** (amd64) as `Run` calls it, every machine-code callee proved: expmc's `IExp.ensCl` (premises = the
Janus runtime contracts only), call depth `43736`, `48` bytes above (`RunIface.ExpSpecA` = `IExp.ExpSpecA`, same text). -/
theorem expA (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh) :
    RunIface.ExpSpecA impl R 43736 48 :=
  IExp.ensCl impl hap R hgr hmc hmv hmz hmk hno hwb hget hput (Nat.le_refl _) (by decide)

end Closed

set_option maxHeartbeats 64000000 in
/-- **Row 1, amd64, EIP-7823 success**, every machine-code callee proved (`(*Int).Mod`, `(*Int).exp`, `(*Int).Bytes`);
premises: the Janus runtime contracts only; the Pool shape `S` is a binder fixed by the precondition. -/
theorem okC (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (W : Nat) (hW : 616 + 43736 ≤ W) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => S = StkShape ∧ RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') := by
  intro ret hret s hs ⟨hS, hpre⟩
  subst hS
  exact okA impl hap R hmk hmkz hmv hmz hno hgr hmc hwb StkShape hget hput hwb4 43736 48
    (Closed.expA impl hap R hmk hmv hmz hno hgr hmc hwb hget hput) W hW (by omega) (by decide) (by decide)
    (by decide) b L c p len cp ret hret s hs ⟨rfl, hpre⟩

end FvModexp.Amd64.Run

open Janus.Contracts.Toy Janus.Contracts.LiveSat

namespace FvModexp.Amd64.Run.WitnessA

open FvModexp.Amd64.AsmWit
open FvModexp.Amd64.Run.Witness (hret)
open FvModexp.Amd64.Run.WitnessOk (s2 c2 p2 WW bW setup2 pre2 compute2 site_mkz site_mvz)
open FvModexp.Amd64.ModRowW (callP site_put)

set_option maxRecDepth 100000

/-- The runtime models of every contract `correctness` assumes, on the shared witness runtime. -/
theorem m_mk : MakesliceLiveContract64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.makeslice") 4096 R := by
  rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _
theorem m_mkz : MakesliceZeroLive64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.makeslice") 4096 R := by
  rw [WStubs.addr_mk]; exact WStubs.mkz [] (by intro t ht; simp at ht) _
theorem m_mv : MemmoveLive64 (Extracted.program.ofImpl WStubs.impl) (Extracted.program.contractAddr "runtime.memmove")
    4096 R := by rw [WStubs.addr_mv]; exact WStubs.mv R
theorem m_mvz : MemmoveZeroLive64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.memmove") 4096 R := by rw [WStubs.addr_mv]; exact WStubs.mvz R
theorem m_no : NewobjectLiveContract64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.newobject") 4096 R := by
  rw [WStubs.addr_no]; exact WStubs.no [] (by intro t ht; simp at ht) _
theorem m_gr : GrowsliceLiveContract64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.growslice") 4096 R := by
  rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _
theorem m_cl : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R := by rw [WStubs.addr_cl]; exact WStubs.cl R
theorem m_wb2 : WbLiveContract64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 := by
  rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _
theorem m_wb4 : WbLiveContract64 (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 := by
  rw [WStubs.addr_wb4]; exact WStubs.wb4 [] (by intro t ht; simp at ht) _
theorem m_get : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R WitSitesAmd64.stkT StkShape := by
  rw [WStubs.addr_get]; exact WStubs.get [] _ _ _
theorem m_put : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl WStubs.impl)
    (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R WitSitesAmd64.stkT StkShape := by
  rw [WStubs.addr_put]; exact WStubs.put [] (by intro t ht; simp at ht) _ _ _

/-- The cost bound at the witness: lengths `1, 1, 1` fit the toy budget `bW = 0x300000` (heap `2^22`). -/
theorem budget2 : RunAmd64.okBudget (parseLengths (bytesAt s2.mem p2.toNat (99 : BitVec 64).toNat)) ≤ bW := by
  decide +kernel

/-- The witness statement (the amd64 twin of `Arm64.RunSucc.Witness.nonvacuous`), for an exp call depth `stkM`. -/
def Stmt (stkM : Nat) : Prop :=
  ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (c p len cp : BitVec 64) (ret : Nat) (s : State) (W : Nat),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R WitSitesAmd64.stkT StkShape ∧
    Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R WitSitesAmd64.stkT StkShape ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    616 + stkM ≤ W ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp] s ∧
    StkShape = StkShape ∧ RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
    RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
    RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
    RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
    LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧
    compute (bytesAt s.mem p.toNat len.toNat) (parseLengths (bytesAt s.mem p.toNat len.toNat)) = ⟨#[5]⟩ ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      WitSitesAmd64.mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      ((MakeslicePre64 4096 s_c ∧ StackRoom64 s_c 4096 3 ∧
        LiveAt R (Extracted.program.contractAddr "runtime.makeslice") [(s_c.regs 0).toNat, (s_c.regs 3).toNat,
          (s_c.regs 1).toNat] L b 0 (s_c.regs 14).toNat s_c.mem (liveWin64 s_c 4096 3)) ∧
        typSize s_c.mem (s_c.regs 0).toNat * (s_c.regs 1).toNat = 0 ∧
        Outside (s_c.regs 0).toNat 16 (calleeStack64 s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      WitSitesAmd64.mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      ((s_c.regs 1).toNat = 0 ∧ MemPre64 4096 3 s_c ∧
        LiveMemAt64 R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 3).toNat,
          (s_c.regs 1).toNat] L b s_c (liveWin64 s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      WitSitesAmd64.noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      WitSitesAmd64.grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      WitSitesAmd64.clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      WitSitesAmd64.wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      WitSitesAmd64.getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      WitSitesAmd64.putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      WitSitesAmd64.wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s')

set_option maxHeartbeats 64000000 in
/-- The witness, given `(*Int).exp`'s interface at the witness runtime (call depth `stkM ≤ WW - 616`). -/
theorem nonvacuous_of (stkM aboveM : Nat) (hE : RunIface.ExpSpecA WStubs.impl R stkM aboveM)
    (hW : 616 + stkM ≤ WW) (hab : aboveM ≤ 144) (hk : 41800 ≤ stkM) (ha : 16 ≤ aboveM) : Stmt stkM :=
  ⟨WStubs.impl, R, bW, [], c2, p2, 99, 99, RET, s2, WW, WStubs.hap, m_mk, m_mkz, m_mv, m_mvz, m_no, m_gr, m_cl, m_wb2,
    m_get, m_put, m_wb4, hW, hret, setup2, rfl,
    (pre2 budget2).1, (pre2 budget2).2.1, (pre2 budget2).2.2.1, (pre2 budget2).2.2.2.1, (pre2 budget2).2.2.2.2.1,
    (pre2 budget2).2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.2.1,
    (pre2 budget2).2.2.2.2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.2.2.2.1, (pre2 budget2).2.2.2.2.2.2.2.2.2.2,
    compute2,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mkA IntBytes.uint8T 0 0, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mkz _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact site_put _⟩,
    ⟨[], 0x1000, callS WStubs.wb4A 0 0 0, by rw [WStubs.addr_wb4]; rfl, by rw [WStubs.addr_wb4]; exact site_wb _ _⟩,
    Run.okA WStubs.impl WStubs.hap R m_mk m_mkz m_mv m_mvz m_no m_gr m_cl m_wb2 StkShape m_get m_put m_wb4 stkM aboveM hE
      WW hW (by decide) hab hk ha bW [] c2 p2 99 99 RET hret s2 setup2 ⟨rfl, pre2 budget2⟩⟩

set_option maxHeartbeats 64000000 in
/-- The witness, every callee closed (`(*Int).exp` = `Run.Closed.expA` at the witness runtime, depth 43736). -/
theorem nonvacuousC : Stmt 43736 :=
  nonvacuous_of 43736 48 (Run.Closed.expA WStubs.impl WStubs.hap R m_mk m_mv m_mvz m_no m_gr m_cl m_wb2 m_get m_put)
    (by decide) (by decide) (by decide) (by decide)

end FvModexp.Amd64.Run.WitnessA
