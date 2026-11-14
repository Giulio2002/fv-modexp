import FvModexp.Proofs.Arm64.Exp.IExpSpec
import FvModexp.Proofs.Arm64.Exp.IExpClD
import FvModexp.Proofs.Arm64.Exp.EvInst
import FvModexp.Proofs.Arm64.Exp.NCap

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64) with the TIGHT-COSTS callee instances: `IExp.ensClQ : ExpSpecM …` (agent expmc s43)

`IExp.ensCl` (IExpCl.lean) with the Q-form callees consumed through the bridges of ExpQ/Bridge.lean
(NOTES-conventions "[expmc s43] TIGHT COSTS — expmc's Q-form EXPORTS + BRIDGES"):
* `nat.div` (the windows' calls, `DHyps.div`): asm's Q-form `ExpSlow.DivHypLGQ … (Q.NatDiv.costQ Q.drsCQ)` (premise `hdQ`
  until asm's `Q.NatDiv.ensCLG` lands) through `Q.divL_of_Q` — cost `clFQ = Q.divBr (Q.NatDiv.costQ Q.drsCQ)`;
* `nat.expNNSlow` (`DHyps.slow`): expmc's Q-form `Q.ExpSlow.hyp` with `nat.sqr` = `Q.ExpSlow.sqrGQ` (divmc's
  `Q.NatSqr.ens`), `nat.mul` = `Q.ExpSlow.mulGQ`
  (divmc's `Q.NatMul.ens`, ExpQ/SlowMuGQ), `nat.div` = `hdQ`; bridged by `Q.slow_of_Q` — cost `clSQ`;
* `nat.rem`: asm's Q-form `NHyp.RemHypQ` (premise `hremQ` until `Q.NatRem.ensCR` lands) through `Q.rem_of_Q` — `clRQ`;
* `nat.expNNPowerOfTwo` / `nat.expNNEven`: infra's current closed instances (`p2Cl`, `ExpEven.fullI`), cost `clP`.
Remaining premises: the runtime contracts, the window depths, the three Q callee summaries above, and `BudClQ`
(the text of `BudCl` at these cost instances, against `RunIface.ExpBudget`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)

namespace FvModexp.Arm64.IExp

/-- the dominating bound of `expNNEven`'s inner budget -/
abbrev clBUQ : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE clFQ clRQ clSQ clP)
/-- the dominating bound of `expNNEven`'s inner cost -/
abbrev clCUQ : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost clFQ clRQ clSQ clP)
/-- `nat.expNNEven`'s cost -/
abbrev clEQ : Nat → Nat → Nat → Nat → Nat := ExpEven.costE clFQ clRQ clSQ clP clBUQ clCUQ sqrCQ mulCQ (ExpEven.mulBrE mulCQ)

/-- the closed allocation-budget bound of `(*Int).exp` at the TIGHT-COSTS instances (the text of `BudCl`; PATH MAX) -/
def BudClQ : Prop :=
  ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    24 + (makeCost 1 + max (clRQ 0 xl n) (makeCost n + max (ExpN.maxC clSQ clEQ 0 xl yl n)
      (max (clP 0 xl yl lm) (ExpOdd.OBud clFQ n xl yl 0)))) ≤ RunIface.ExpBudget (max (max xl yl) n) yl ∧
    24 + ExpN.NCost clFQ clRQ (ExpN.maxC clSQ clEQ) clP xl yl n 0 lm ≤ RunIface.ExpBudget (max (max xl yl) n) yl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64), `ExpSpecM`, with the TIGHT-COSTS callee instances (see the module doc) -/
theorem ensClQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hdQ : ExpSlow.DivHypLGQ impl R NatDiv.names 41504 112 (Q.NatDiv.costQ Q.drsCQ))
    (hremQ : NHyp.RemHypQ impl R LibRem.names 41712 112 NatRem.need (Q.NatDiv.costQ Q.drsCQ))
    {K KN stkE : Nat} (hKN : 70720 ≤ KN) (hk1 : 71168 ≤ stkE) (hk2 : stkE ≤ 2 ^ 20 + 336) (hk3 : KN + 1648 ≤ stkE)
    (hstkE : stkE ≤ K + 1056) (hK20 : K + 288 ≤ 2 ^ 20)
    {stk above : Nat} (hK : K + 1632 ≤ stk) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above) (hbud : BudClQ) :
    ExpSpecM impl R stk above := by
  have hDN := dhypsQ hap hmk hgr hmc hmv hno hwb hdQ hKN
  have hD := dhypsQ hap hmk hgr hmc hmv hno hwb hdQ (K := K) (by omega)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need clRQ := Q.rem_of_Q hremQ
  have hNE : EvenHyp.ExpNNHypNE impl R KN clFQ NatRem.need clRQ ExpSlow.need P2D.needP clSQ clP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem rem_n rem_11 (by omega) b L zp zl zc st xp xl xc yp yl yc mp n mc slow
  have hEv := ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by omega) (by omega)
    rem_mono slow_mono p2_mono (bU := clBUQ) (cU := clCUQ) (Exp.dom _) (Exp.dom _) hk1 hk2 hk3
  exact ExpSpecX.toSpecM <|
    ens impl hap R hD hEv hstkE (fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn (libNE_code impl hap) (hget L b))
      (NewobjectLiveContract.of_codeIn (libNE_code impl hap) hno)
      (fun L b rs => Janus.Contracts.EqHashModel.Summary.of_codeIn (libFree_code impl hap) (hput L b rs)) hRem rem_n rem_11 (by omega)
      (WbLiveContract.of_codeIn (libExp_code impl hap) hwb) hK (by omega) hK20 h4416 hab need_bounds hbud

end FvModexp.Arm64.IExp
