import FvModexp.Proofs.Arm64.Exp.IExpClN
import FvModexp.Proofs.Arm64.Exp.P2Wit
import FvModexp.Proofs.Arm64.Exp.CalleeInstP2Q
import FvModexp.Proofs.Arm64.Exp.NFun
import FvModexp.Proofs.Arm64.Exp.DivInstN
import FvModexp.Proofs.Arm64.ExpQ.SlowSumQ
import FvModexp.Proofs.Arm64.ExpQ.SlowSqGQ
import FvModexp.Proofs.Arm64.ExpQ.SlowMuGQ
import FvModexp.Proofs.Arm64.ExpQ.Bridge
import FvModexp.Proofs.Arm64.Exp.NFunNE
import FvModexp.Proofs.Arm64.Exp.EvCost
import FvModexp.Proofs.Arm64.Exp.CalleeInst0
import FvModexp.Proofs.Arm64.Nat.RemDefs

set_option autoImplicit false

/-!
# `nat.expNN`'s callee shapes (arm64), every callee proved, TIGHT-COSTS (Q-form) instances: `IExp.dhypsQ`

`IExp.slowClQ` (`nat.expNNSlow`, Q-form inside), `IExp.p2Cl` (`nat.expNNPowerOfTwo`), `IExp.dhypsQ` (`ExpN.DHyps` at
`K ≥ 70720`), the bridged cost instances `clFQ`/`clRQ`/`clSQ`/`clP` and the need facts (`rem_mono`/`slow_mono`/`p2_mono`/
`need_bounds`). Split by expmc s69 (statements unchanged, moved verbatim from Exp/IExpClD (infra s52), Exp/IExpCl and
ExpQ/IExpClQ) so that this module does NOT reach the retired old `nat.sqr` SCC (`Exp/SlowSqG` → `Nat/SqrHypX`):
`nat.sqr` = `Q.ExpSlow.sqrGQ` (ExpQ/SlowSqGQ, divmc's `Q.NatSqr.ens`). The old-cost shapes `slowCl`/`slowC`/`dhyps`
are in Exp/IExpClDO.lean.
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

open FvModexp.Arm64.CalleeInstQ FvModexp.Arm64.P2WitQ in
/-- **`nat.expNNPowerOfTwo`** (arm64), every callee proved (infra's `P2D.ens` + `CalleeInstQ`/`P2WitQ`: the P2 chain in
Q-form, divmc s42), window `71776` -/
theorem p2Cl {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    NHyp.P2Hyp impl R LibW.names 71776 112 P2D.needP (P2D.cP sqrCQ mulCQ) := by
  have hW := CalleeInst.sqrWX_eq
  exact P2D.ens hap sub nf2 nf4 nfP nfD hgr hmc hmv hmk hno hwb (kcP := NatSqr.sqrWX) (by omega)
    (sn hap hgr hmc hwb) (by omega) (by omega) (sq hap hgr hmc hmv hmk hwb) (Nat.le_refl _) (by omega) sqm
    (mu hap hgr hmc hmv hmk hwb) (by rw [CalleeInst.mulWX_eq]; omega) (by omega) mum (tr hap hmv hmk) (by omega) (by omega)
    (rh hap hmv hmk) (by omega) (lh hap hmc hmv hmk) (by omega) 71776 (by omega) (by omega) (by omega) (by omega)

/-- the slow / even need and cost functions of the closed `(*Int).exp` -/
abbrev needSE : Nat → Nat → Nat → Nat :=
  ExpN.addN ExpSlow.need (ExpEven.needE NatRem.need ExpSlow.need P2D.needP)

/-! ### The closed cost functions and the cost facts (expmc s42, TIGHT COSTS; as top's `Run.Closed`) -/

/-- `nat.expNNPowerOfTwo`'s cost -/
abbrev clP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrCQ mulCQ
/-- `nat.div`'s bridged cost (the windows' calls) -/
abbrev clFQ : Nat → Nat → Nat → Nat := Q.divBr (Q.NatDiv.costQ Q.drsCQ)
/-- `nat.rem`'s bridged cost -/
abbrev clRQ : Nat → Nat → Nat → Nat := Q.brC (Q.NatDiv.costQ Q.drsCQ) NatRem.need
/-- `nat.expNNSlow`'s bridged cost (Q-form inside) -/
abbrev clSQ : Nat → Nat → Nat → Nat → Nat :=
  Q.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) Q.ExpSlow.needH
theorem rem_mono : ∀ x a a', a ≤ a' → NatRem.need x a ≤ NatRem.need x a' := fun _ _ _ _ => by
  simp only [NatRem.need]; omega

theorem slow_mono : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a' := fun x _ a a' h => by
  simp only [ExpSlow.need]
  split <;> split <;> omega

theorem p2_mono : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a' := fun _ _ _ _ _ => Nat.le_refl _

/-- the stack-need bound of `IExp.ens` (`hneed`) for the closed needs -/
theorem need_bounds : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    NatRem.need xl n ≤ 2 ^ 16 ∧ needSE xl yl n ≤ 2 ^ 16 ∧ P2D.needP xl yl lm ≤ 2 ^ 16 := by
  intro xl yl n lm hx _ _ hn _
  refine ⟨by simp only [NatRem.need]; omega, ?_, by simp only [P2D.needP]; omega⟩
  simp only [needSE, ExpN.addN, ExpEven.needE, ExpSlow.need, NatRem.need, P2D.needP, StackNat.rnd,
    if_pos (And.intro hx hn)]
  omega

/-- **`nat.expNNSlow`** (arm64), Q-form inside, bridged to `NHyp.SlowHyp`, window `71776` -/
theorem slowClQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {nsD : List String} {kD aD : Nat} {dvC : Nat → Nat → Nat} (hdv : ExpSlow.DivHypLGQ impl R nsD kD aD dvC)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnfD : nsD.contains ExpSlow.fn = false)
    (haD : aD ≤ 120) (hkD : kD ≤ 71344) :
    NHyp.SlowHyp impl R LibW.names 71776 112 ExpSlow.need
      (Q.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ dvC) Q.ExpSlow.needH) := by
  have hW := CalleeInst.sqrWX_eq
  have e1 : ∀ x, NatSqr.names.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.true_or]
  have e2 : ∀ x, NatMul.names.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.true_or, Bool.or_true]
  have e3 : ∀ x, nsD.contains x = true → (nsSl nsD).contains x = true := fun x h => by
    simp only [nsSl, List.contains_append, h, Bool.or_true]
  have hsq : Q.ExpSlow.SqrHypGQ impl R (nsSl nsD) NatSqr.sqrWX 64 sqrCQ := fun H b L z zl zc st x xl xc =>
    ens_widen hap e1 (Q.ExpSlow.sqrGQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc)
  have hmu : Q.ExpSlow.MulHypGQ impl R (nsSl nsD) mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
    ens_widen hap e2 (Q.ExpSlow.mulGQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc y yl yc)
  have hdv' : ExpSlow.DivHypLGQ impl R (nsSl nsD) kD aD dvC := fun H b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
    ens_widen hap e3 (hdv H b L z zl zc st z2 z2l z2c u ul uc v vl vc)
  exact Q.slow_of_Q (Q.ExpSlow.hyp hap (nsSl_sub hnsD) (nsSl_fn hnfD) hsq hmu hdv' (by omega) (by omega) haD hmk hmv
    (by omega) (by omega) (by omega) (by rw [CalleeInst.mulWX_eq]; omega) (by omega))

/-- `nat.expNN`'s callee shapes at window level `K` (`70720 ≤ K`) with the TIGHT-COSTS instances -/
theorem dhypsQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hdQ : ExpSlow.DivHypLGQ impl R NatDiv.names 41504 112 (Q.NatDiv.costQ Q.drsCQ))
    {K : Nat} (hK : 70720 ≤ K) :
    ExpN.DHyps impl R K clFQ ExpSlow.need P2D.needP clSQ (P2D.cP sqrCQ mulCQ) NatDiv.names 41504 LibW.names 71776
      LibW.names 71776 :=
  { mkN := MakesliceLiveContract.of_codeIn (libN_code impl hap) hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr,
    wb := hwb, div := Q.divL_of_Q hdQ.toL, hnsD := DivInstN.ns_sub,
    hnsW4 := DivInstN.ns_w4, hnsW2 := DivInstN.ns_w2, hKD := by omega,
    slow := slowClQ hap hmk hgr hmc hmv hwb hdQ DivInstN.ns_sub div_fn (by omega) (by omega),
    hnsS := w_n, hn11S := w_11, hKS := by omega,
    p2 := p2Cl hap hmk hgr hmc hmv hno hwb, hnsP := w_n, hn11P := w_11, hKP := by omega }

end FvModexp.Arm64.IExp
