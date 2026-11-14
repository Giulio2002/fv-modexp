import FvModexp.Proofs.Arm64.Exp.IExpClD
import FvModexp.Proofs.Arm64.Exp.SlowSum
import FvModexp.Proofs.Arm64.Exp.SlowSqG
import FvModexp.Proofs.Arm64.Exp.EvMulG
import FvModexp.Proofs.Arm64.Exp.DivInst
import FvModexp.Proofs.Arm64.Nat.DivC
import FvModexp.Proofs.Arm64.Nat.DivCG

set_option autoImplicit false

/-!
# `nat.expNN`'s callee shapes (arm64) at the OLD cost instances: `IExp.slowCl`/`slowC`/`dhyps` (split out of
Exp/IExpClD by expmc s69, statements and proofs unchanged)

These use the old `nat.sqr`/`nat.mul` summaries (`ExpSlow.sqrG`, `ExpEven.NatMulG.hypG`) and asm's old-cost `nat.div`;
only the old-cost `(*Int).exp` (`IExp.ensCl`, Exp/IExpCl.lean) imports this module. The release path uses the Q-form
`IExp.dhypsQ` (Exp/IExpClD.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)
open Janus.Contracts.EqHashModel (CodeIn)

namespace FvModexp.Arm64.IExp

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
  have hW := CalleeInst.sqrWX_eq
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
      (P2D.cP sqrCQ mulCQ) NatDiv.names 41504 LibW.names 71776 LibW.names 71776 :=
  { mkN := MakesliceLiveContract.of_codeIn (libN_code impl hap) hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr,
    wb := hwb, div := NatDiv.ensCL impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub,
    hnsW4 := DivInst.ns_w4, hnsW2 := DivInst.ns_w2, hKD := by omega,
    slow := slowC hap hmk hgr hmc hmv hmz hwb, hnsS := w_n, hn11S := w_11, hKS := by omega,
    p2 := p2Cl hap hmk hgr hmc hmv hno hwb, hnsP := w_n, hn11P := w_11, hKP := by omega }

end FvModexp.Arm64.IExp
