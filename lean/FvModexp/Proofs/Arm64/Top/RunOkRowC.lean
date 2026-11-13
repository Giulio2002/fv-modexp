import FvModexp.Proofs.Arm64.Top.RunModC
import FvModexp.Proofs.Arm64.Top.RunOkRow
import FvModexp.Proofs.Arm64.Exp.IExpCl
import FvModexp.Proofs.Arm64.Nat.DivCG
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# Row 1, arm64, success path with EVERY machine-code callee proved (agent top s26)

`correctness_okC` = `Run.correctness_ok` (`ensOkLib`: Run's own code, `(*Int).Bytes` = `IntBytes.bytesSpec_at`) with
* `(*Int).Mod` (`hM`) = `modSpecM_C` (divmc's `IMod.ens` + `IMod.bud`, asm's `NatDiv.ensMC`);
* `(*Int).exp` (`hE`) = `expC` below = expmc's `IExp.ensCl` body (IExpCl.lean: `IExp.dhyps` with every callee proved)
  EXCEPT the cost-dominating bounds (ensCl's `hNB`/`hNC` are monotonicity of `NBudE`/`NCost` in the modulus length,
  FALSE per Common/NCostU — so ensCl itself cannot be applied):
  - `nat.expNNEven`'s dominating cost bounds `bU`/`cU` := `Exp.supU` of `NBudE`/`NCost` (expmc's `Common/NCostU`:
    `NBudE`/`NCost` are NOT monotone in the modulus length, so `IExp.ensCl`'s `hNB`/`hNC` with `bU := NBudE` are not
    provable; `Exp.dom` discharges the `supU` form for every function),
  - the monotonicity premises `hRm hSm hPm` and the stack-need bound `hneed` proved here (`need_bounds`);
* windows fixed: inner `nat.expNN` at `KN = 70720`, `expNNEven` at `stkE = 72368`, outer `nat.expNN` at `K = 71312`.

STILL PREMISES (besides the Janus runtime contracts on `Extracted.program.ofImpl impl`): `hbud` — the allocation-budget
bound of `(*Int).exp` (`IExp.ens`'s `hbud` for the concrete callee cost functions: the closed cost of `nat.expNN` is at
most `RunIface.ExpBudget`). Pure arithmetic about the cost functions; no machine code involved.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open Janus.Contracts.EqHashModel
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run.Closed

/-- `nat.div`'s cost (both `nat.div` instances and `expNNSlow`'s `div`) -/
abbrev cF : Nat → Nat → Nat → Nat := NatDiv.cost DivRec.drsC
/-- `nat.rem`'s cost -/
abbrev cR : Nat → Nat → Nat → Nat := NatRem.cost cF
/-- `nat.expNNSlow`'s cost -/
abbrev cS : Nat → Nat → Nat → Nat → Nat := ExpSlow.cost sqrC mulC cF
/-- `nat.expNNPowerOfTwo`'s cost -/
abbrev cP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrC mulC
/-- the dominating bound of `expNNEven`'s inner budget -/
abbrev bUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE cF cR cS cP)
/-- the dominating bound of `expNNEven`'s inner cost -/
abbrev cUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost cF cR cS cP)
/-- `nat.expNNEven`'s cost -/
abbrev cE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE cF cR cS cP bUC cUC sqrC mulC mulC

/-- the closed allocation-budget bound of `(*Int).exp` (`IExp.ens`'s `hbud` for the concrete callee costs) -/
def BudOK : Prop :=
  ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    24 + (makeCost 1 + makeCost n + cR 0 xl n + ExpN.addC cS cE 0 xl yl n + cP 0 xl yl lm +
      ExpOdd.OBud cF n xl yl 0) ≤ RunIface.ExpBudget (max (max xl yl) n) yl ∧
    24 + ExpN.NCost cF cR (ExpN.addC cS cE) cP xl yl n 0 lm ≤ RunIface.ExpBudget (max (max xl yl) n) yl

theorem rem_mono : ∀ x a a', a ≤ a' → NatRem.need x a ≤ NatRem.need x a' := fun _ _ _ _ => by
  simp only [NatRem.need]; omega

theorem slow_mono : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a' := fun x _ a a' h => by
  simp only [ExpSlow.need]
  by_cases h1 : x ≤ 128 ∧ a' ≤ 128
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1]; split <;> omega

theorem p2_mono : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a' := fun _ _ _ _ _ => Nat.le_refl _

/-- the stack-need bound of `IExp.ens` (`hneed`) for the concrete needs -/
theorem need_bounds : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    NatRem.need xl n ≤ 2 ^ 16 ∧ IExp.needSE xl yl n ≤ 2 ^ 16 ∧ P2D.needP xl yl lm ≤ 2 ^ 16 := by
  intro xl yl n lm hx _ _ hn _
  refine ⟨by simp only [NatRem.need]; omega, ?_, by simp only [P2D.needP]; omega⟩
  simp only [IExp.needSE, ExpN.addN, ExpEven.needE, ExpSlow.need, NatRem.need, P2D.needP, StackNat.rnd,
    if_pos (And.intro hx hn)]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it, every machine-code callee proved; premise `hbud : BudOK` (cost
arithmetic) and the Janus runtime contracts. -/
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
    (hbud : BudOK) {stk above : Nat} (hK : 72944 ≤ stk) (hab : 48 ≤ above) :
    RunIface.ExpSpec impl R stk above := by
  have hDN := IExp.dhyps hap hmk hgr hmc hmv hmz hno hwb (K := 70720) (Nat.le_refl _)
  have hD := IExp.dhyps hap hmk hgr hmc hmv hmz hno hwb (K := 71312) (by decide)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need cR :=
    NatRem.ensC impl hap R hgr hmc hwb hmk hmv hmz
  have hNE : EvenHyp.ExpNNHypNE impl R 70720 cF NatRem.need cR ExpSlow.need P2D.needP cS cP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem IExp.rem_n IExp.rem_11 (by decide) b L zp zl zc st xp xl xc yp yl yc mp n
        mc slow
  have hEv := ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by decide) (by decide)
    rem_mono slow_mono p2_mono (bU := bUC) (cU := cUC) (Exp.dom _) (Exp.dom _) (stk := 72368) (by decide) (by decide)
    (by decide)
  exact IExp.ExpSpecX.toSpecM <|
    IExp.ens impl hap R hD hEv (by decide) (fun L b => Summary.of_codeIn (IExp.libNE_code impl hap) (hget L b))
      (NewobjectLiveContract.of_codeIn (IExp.libNE_code impl hap) hno)
      (fun L b rs => Summary.of_codeIn (IExp.libFree_code impl hap) (hput L b rs)) hRem IExp.rem_n IExp.rem_11
      (by decide) (WbLiveContract.of_codeIn (IExp.libExp_code impl hap) hwb) (by omega) (by decide) (by decide)
      (by omega) hab need_bounds hbud

end FvModexp.Arm64.Run.Closed

namespace FvModexp.Arm64.Run

set_option maxHeartbeats 64000000 in
/-- **Row 1, arm64, EIP-7823 success**, every machine-code callee proved (`(*Int).Mod`, `(*Int).exp` with the whole
`nat` chain, `(*Int).Bytes`); premises: the Janus runtime contracts and the cost arithmetic `Closed.BudOK`. -/
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
    (hbud : Closed.BudOK)
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
    (Closed.expC impl hap R hmk hgr hmc hmv hmz hno hwb hget hput hbud (Nat.le_refl _) (by decide))
    W hW (by omega) (by decide) (by decide) (by decide) b L c p len cp

end FvModexp.Arm64.Run
