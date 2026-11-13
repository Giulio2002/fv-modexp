import FvModexp.Proofs.Arm64.Exp.IExpSpec
import FvModexp.Proofs.Arm64.Exp.IExpClN
import FvModexp.Proofs.Arm64.Exp.SlowSum
import FvModexp.Proofs.Arm64.Exp.SlowSqG
import FvModexp.Proofs.Arm64.Exp.EvMulG
import FvModexp.Proofs.Arm64.Exp.P2Wit
import FvModexp.Proofs.Arm64.Exp.EvInst
import FvModexp.Proofs.Arm64.Exp.NFun
import FvModexp.Proofs.Arm64.Exp.NCap
import FvModexp.Proofs.Arm64.Exp.DivInst
import FvModexp.Proofs.Arm64.Nat.RemC
import FvModexp.Proofs.Arm64.Nat.DivC
import FvModexp.Proofs.Arm64.Nat.DivCG

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
NO open callee premise. Remaining premises: the Janus runtime contracts (on `Extracted.program.ofImpl impl`) and the COST facts — the
monotonicity premises of `fullI` (`hRm hSm hPm hNB hNC`) and `IExp.ens`'s budget bounds `hneed` / `hbud` (functions of the
concrete callee costs, stated with them).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)
open Janus.Contracts.EqHashModel (CodeIn)

namespace FvModexp.Arm64.IExp

theorem nsSl_sub {nsD : List String} (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) :
    ∀ x, (nsSl nsD).contains x = true → LibW.names.contains x = true := by
  intro x hx
  simp only [nsSl, List.contains_append, Bool.or_eq_true] at hx
  rcases hx with (h | h) | h
  · exact sqr_slow x h
  · exact mul_slow x h
  · exact hnsD x h

theorem nsSl_fn {nsD : List String} (hnfD : nsD.contains ExpSlow.fn = false) :
    (nsSl nsD).contains ExpSlow.fn = false := by
  simp only [nsSl, List.contains_append, sqr_fn, mul_fn, hnfD, Bool.or_false]

/-- **`nat.expNNSlow`** (arm64) with `sqr` and `mul` proved (`div` = the premise `hdv`), window `71776` -/
theorem slowCl {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {nsD : List String} {kD aD : Nat} {dvC : Nat → Nat → Nat → Nat} (hdv : ExpSlow.DivHypLG impl R nsD kD aD dvC)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnfD : nsD.contains ExpSlow.fn = false)
    (haD : aD ≤ 120) (hkD : kD ≤ 71344) :
    NHyp.SlowHyp impl R LibW.names 71776 112 ExpSlow.need (ExpSlow.cost sqrC mulC dvC) := by
  have hW := ExpEven.sqrWX_eq
  have e1 : ∀ x, NatSqr.names.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.true_or]
  have e2 : ∀ x, NatMul.names.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.true_or, Bool.or_true]
  have e3 : ∀ x, nsD.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.or_true]
  have hsq : ExpSlow.SqrHypG impl R (nsSl nsD) NatSqr.sqrWX 64 sqrC := fun b L z zl zc st x xl xc =>
    ens_widen hap e1 (ExpSlow.sqrG impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc)
  have hmu : ExpEven.MulHypG impl R (nsSl nsD) mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
    ens_widen hap e2 (ExpEven.NatMulG.hypG impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc y yl yc)
  have hdv' : ExpSlow.DivHypLG impl R (nsSl nsD) kD aD dvC := fun b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    ens_widen hap e3 (hdv b L z zl zc st z2 z2l z2c u ul uc v vl vc)
  exact ExpSlow.hyp hap (nsSl_sub hnsD) (nsSl_fn hnfD) hsq hmu hdv' (by omega) (by omega) haD hmk hmv
    (by omega) (by omega) (by omega) (by rw [CalleeInst.mulWX_eq]; omega) (by omega)

/-- **`nat.expNNSlow`** (arm64), EVERY callee proved (`div` = asm's `NatDiv.ensCLG`), window `71776` -/
theorem slowC {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    NHyp.SlowHyp impl R LibW.names 71776 112 ExpSlow.need (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) :=
  slowCl hap hmk hgr hmc hmv hwb (NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz) DivInst.ns_sub div_fn
    (by omega) (by omega)

open FvModexp.Arm64.CalleeInst FvModexp.Arm64.P2Wit in
/-- **`nat.expNNPowerOfTwo`** (arm64), every callee proved (infra's `P2D.ens` + `CalleeInst`), window `71776` -/
theorem p2Cl {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    NHyp.P2Hyp impl R LibW.names 71776 112 P2D.needP (P2D.cP sqrC mulC) := by
  have hW := sqrWX_eq
  exact P2D.ens hap sub nf2 nf4 nfP nfD hgr hmc hmv hmk hno hwb (kcP := NatSqr.sqrWX) (by omega)
    (sn hap hgr hmc hwb) (by omega) (by omega) (sq hap hgr hmc hmv hmk hwb) (Nat.le_refl _) (by omega) sqm
    (mu hap hgr hmc hmv hmk hwb) (by rw [mulWX_eq]; omega) (by omega) mum (tr hap hmv hmk) (by omega) (by omega)
    (rh hap hmv hmk) (by omega) (lh hap hmc hmv hmk) (by omega) 71776 (by omega) (by omega) (by omega) (by omega)

/-- `nat.expNN`'s callee shapes at window level `K` (`70720 ≤ K`), every one proved -/
theorem dhyps {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {K : Nat} (hK : 70720 ≤ K) :
    ExpN.DHyps impl R K (NatDiv.cost DivRec.drsC) ExpSlow.need P2D.needP (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
      (P2D.cP sqrC mulC) NatDiv.names 41504 LibW.names 71776 LibW.names 71776 :=
  { mkN := MakesliceLiveContract.of_codeIn (libN_code impl hap) hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr,
    wb := hwb, div := NatDiv.ensCL impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub,
    hnsW4 := DivInst.ns_w4, hnsW2 := DivInst.ns_w2, hKD := by omega,
    slow := slowC hap hmk hgr hmc hmv hmz hwb, hnsS := w_n, hn11S := w_11, hKS := by omega,
    p2 := p2Cl hap hmk hgr hmc hmv hno hwb, hnsP := w_n, hn11P := w_11, hKP := by omega }

/-- the slow / even need and cost functions of the closed `(*Int).exp` -/
abbrev needSE : Nat → Nat → Nat → Nat :=
  ExpN.addN ExpSlow.need (ExpEven.needE NatRem.need ExpSlow.need P2D.needP)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it, `ExpSpecM` (= `RunIface.ExpSpec` + `ModX z`), with EVERY callee of
`nat.expNN` proved. Premises: the Janus runtime contracts and the cost facts (`fullI`'s monotonicity `hRm hSm hPm hNB hNC`; `IExp.ens`'s
budget bounds `hneed` / `hbud`). Windows: `nat.expNN` at `K` (outer) and `KN` (inside `expNNEven`). -/
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
    (hRm : ∀ x a a', a ≤ a' → NatRem.need x a ≤ NatRem.need x a')
    (hSm : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a')
    (hPm : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a')
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpEven.NBudE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (P2D.cP sqrC mulC) x y a l k ≤
        ExpEven.NBudE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (P2D.cP sqrC mulC) x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (P2D.cP sqrC mulC) x y a l k ≤
        ExpN.NCost (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (P2D.cP sqrC mulC) x y a' l' k')
    {stk above : Nat} (hK : K + 1632 ≤ stk) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      NatRem.need xl n ≤ 2 ^ 16 ∧ needSE xl yl n ≤ 2 ^ 16 ∧ P2D.needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + NatRem.cost (NatDiv.cost DivRec.drsC) 0 xl n +
        ExpN.addC (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (ExpEven.costE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
            (P2D.cP sqrC mulC)
            (ExpEven.NBudE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC))
              (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) (P2D.cP sqrC mulC))
            (ExpN.NCost (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC))
              (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) (P2D.cP sqrC mulC)) sqrC mulC mulC) 0 xl yl n +
        P2D.cP sqrC mulC 0 xl yl lm + ExpOdd.OBud (NatDiv.cost DivRec.drsC) n xl yl 0) ≤
          RunIface.ExpBudget (max (max xl yl) n) yl ∧
      24 + ExpN.NCost (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC))
        (ExpN.addC (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
          (ExpEven.costE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC)) (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC))
            (P2D.cP sqrC mulC)
            (ExpEven.NBudE (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC))
              (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) (P2D.cP sqrC mulC))
            (ExpN.NCost (NatDiv.cost DivRec.drsC) (NatRem.cost (NatDiv.cost DivRec.drsC))
              (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) (P2D.cP sqrC mulC)) sqrC mulC mulC))
        (P2D.cP sqrC mulC) xl yl n 0 lm ≤ RunIface.ExpBudget (max (max xl yl) n) yl) :
    ExpSpecM impl R stk above := by
  have hDN := dhyps hap hmk hgr hmc hmv hmz hno hwb hKN
  have hD := dhyps hap hmk hgr hmc hmv hmz hno hwb (K := K) (by omega)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need (NatRem.cost (NatDiv.cost DivRec.drsC)) :=
    NatRem.ensC impl hap R hgr hmc hwb hmk hmv hmz
  have hNE : EvenHyp.ExpNNHypNE impl R KN (NatDiv.cost DivRec.drsC) NatRem.need
      (NatRem.cost (NatDiv.cost DivRec.drsC)) ExpSlow.need P2D.needP (ExpSlow.cost sqrC mulC (NatDiv.cost DivRec.drsC)) (P2D.cP sqrC mulC) :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem rem_n rem_11 (by omega) b L zp zl zc st xp xl xc yp yl yc mp n mc slow
  have hEv := ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by omega) (by omega)
    hRm hSm hPm hNB hNC hk1 hk2 hk3
  exact ExpSpecX.toSpecM <|
    ens impl hap R hD hEv hstkE (fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn (libNE_code impl hap) (hget L b))
      (NewobjectLiveContract.of_codeIn (libNE_code impl hap) hno)
      (fun L b rs => Janus.Contracts.EqHashModel.Summary.of_codeIn (libFree_code impl hap) (hput L b rs)) hRem rem_n rem_11 (by omega)
      (WbLiveContract.of_codeIn (libExp_code impl hap) hwb) hK (by omega) hK20 h4416 hab hneed hbud

end FvModexp.Arm64.IExp
