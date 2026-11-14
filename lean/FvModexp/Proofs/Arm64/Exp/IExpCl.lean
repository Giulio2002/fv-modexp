import FvModexp.Proofs.Arm64.Exp.IExpSpec
import FvModexp.Proofs.Arm64.Exp.IExpClDO
import FvModexp.Proofs.Arm64.Exp.EvInst
import FvModexp.Proofs.Arm64.Exp.NCap
import FvModexp.Proofs.Arm64.Nat.RemC

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64) with every `nat.expNN` callee proved: `IExp.ensCl : ExpSpecM …` (agent expmc s41)

`IExp.ens` (`ExpSpecX`, then `toSpecM`) with the callee shapes discharged by the proved summaries:
* `nat.div` (`DHyps.div`): asm's `NatDiv.ensCL` (twice: the outer `DHyps` at `K`, the inner one at `KN`);
* `nat.expNNSlow` (`DHyps.slow`): expmc's `ExpSlow.hyp` with `nat.sqr` = `ExpSlow.sqrG` (divmc's `NatSqr` in the
  empty-tolerant form), `nat.mul` = infra's `ExpEven.NatMulG.hypG`, `nat.div` = asm's `NatDiv.ensCLG` (`ExpSlow.DivHypLG`);
* `nat.expNNPowerOfTwo` (`DHyps.p2`): infra's `P2D.ens` with `CalleeInst`'s closed callees (as `P2DRow`);
* `nat.rem`: asm's `NatRem.ensC`;
* `nat.expNNEven`: infra's `ExpEven.fullI`, whose inner `nat.expNN` calls are expmc's `ExpN.ens_noEven` on a second
  `DHyps` at `KN` (`ExpNNHypNE.toNE1`).
NO open callee premise. Remaining premises: the Janus runtime contracts (on `Extracted.program.ofImpl impl`), the window
depths and the closed budget bound `BudCl` (s42: the monotonicity and stack-need facts are proved here; `BudCl` is
owned by divmc (`Run.Closed.BudOK`); the slack-budget discharge is drafted in scripts/gen/IExpClB.lean.draft, waiting for divmc's ExpBud* modules to compile).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)
open Janus.Contracts.EqHashModel (CodeIn)

namespace FvModexp.Arm64.IExp

/-- `nat.div`'s cost -/
abbrev clF : Nat → Nat → Nat → Nat := NatDiv.cost DivRec.drsC
/-- `nat.rem`'s cost -/
abbrev clR : Nat → Nat → Nat → Nat := NatRem.cost clF
/-- `nat.expNNSlow`'s cost -/
abbrev clS : Nat → Nat → Nat → Nat → Nat := ExpSlow.cost sqrC mulC clF
/-- the dominating bound of `expNNEven`'s inner budget (`Exp.supU`: `NBudE` is not monotone in the modulus length) -/
abbrev clBU : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE clF clR clS clP)
/-- the dominating bound of `expNNEven`'s inner cost -/
abbrev clCU : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost clF clR clS clP)
/-- `nat.expNNEven`'s cost -/
abbrev clE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE clF clR clS clP clBU clCU sqrCQ mulCQ (ExpEven.mulBrE mulCQ)

/-- the closed allocation-budget bound of `(*Int).exp` (`IExp.ens`'s `hbud` for the closed callee costs; the same
text as top's `Run.Closed.BudOK`) -/
def BudCl : Prop :=
  ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    24 + (makeCost 1 + max (clR 0 xl n) (makeCost n + max (ExpN.maxC clS clE 0 xl yl n)
      (max (clP 0 xl yl lm) (ExpOdd.OBud clF n xl yl 0)))) ≤ RunIface.ExpBudget (max (max xl yl) n) yl ∧
    24 + ExpN.NCost clF clR (ExpN.maxC clS clE) clP xl yl n 0 lm ≤ RunIface.ExpBudget (max (max xl yl) n) yl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it, `ExpSpecM` (= `RunIface.ExpSpec` + `ModX z`), with EVERY callee of
`nat.expNN` proved. Premises: the Janus runtime contracts, the window depths, and the closed budget bound `BudCl`
(pure cost arithmetic). The monotonicity facts of `fullI` are proved (`rem_mono`/`slow_mono`/`p2_mono`; `NBudE`/`NCost`
enter through their box maxima `Exp.supU`, dominated by `Exp.dom`), and so is the stack-need bound (`need_bounds`).
Windows: `nat.expNN` at `K` (outer) and `KN` (inside `expNNEven`). -/
theorem ensCl (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K KN stkE : Nat} (hKN : 70720 ≤ KN) (hk1 : 71168 ≤ stkE) (hk2 : stkE ≤ 2 ^ 20 + 336) (hk3 : KN + 1648 ≤ stkE)
    (hstkE : stkE ≤ K + 1056) (hK20 : K + 288 ≤ 2 ^ 20)
    {stk above : Nat} (hK : K + 1632 ≤ stk) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above) (hbud : BudCl) :
    ExpSpecM impl R stk above := by
  have hDN := dhyps hap hmk hgr hmc hmv hmz hno hwb hKN
  have hD := dhyps hap hmk hgr hmc hmv hmz hno hwb (K := K) (by omega)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need clR :=
    NatRem.ensC impl hap R hgr hmc hwb hmk hmv hmz
  have hNE : EvenHyp.ExpNNHypNE impl R KN clF NatRem.need clR ExpSlow.need P2D.needP clS clP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem rem_n rem_11 (by omega) b L zp zl zc st xp xl xc yp yl yc mp n mc slow
  have hEv := ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by omega) (by omega)
    rem_mono slow_mono p2_mono (bU := clBU) (cU := clCU) (Exp.dom _) (Exp.dom _) hk1 hk2 hk3
  exact ExpSpecX.toSpecM <|
    ens impl hap R hD hEv hstkE (fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn (libNE_code impl hap) (hget L b))
      (NewobjectLiveContract.of_codeIn (libNE_code impl hap) hno)
      (fun L b rs => Janus.Contracts.EqHashModel.Summary.of_codeIn (libFree_code impl hap) (hput L b rs)) hRem rem_n rem_11 (by omega)
      (WbLiveContract.of_codeIn (libExp_code impl hap) hwb) hK (by omega) hK20 h4416 hab need_bounds hbud

end FvModexp.Arm64.IExp
