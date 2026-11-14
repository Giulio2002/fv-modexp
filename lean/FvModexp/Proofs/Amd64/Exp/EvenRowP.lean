import FvModexp.Proofs.Amd64.Exp.EvInst
import FvModexp.Proofs.Amd64.Exp.NCap
import FvModexp.Proofs.Amd64.Exp.P2DRow
import FvModexp.Proofs.Amd64.Exp.SlowQStmt
import FvModexp.Proofs.Amd64.Exp.SlowDefs
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64), PREMISE FORM on `nat.expNNSlow` (agent asm s73; staging for the amd64 `EvenRow`)

`sumP` = divmc's `ExpEven.fullI` with every callee closed EXCEPT the amd64 `nat.expNNSlow` (expmc, in progress): the
inner `nat.expNN` is expmc's `ExpN.hypNE1` on `ExpN.DHyps` with `div` = `DivInst.hyp` (41512), `p2` = `P2DRow.hyp`
(42520), `slow` = `Q.ExpSlow.slow_of_Q hSQ` (the PREMISE `hSQ : NHyp.SlowHypQ …` at expmc's announced closed shape:
need `ExpSlow.need`, level twin `Q.ExpSlow.needH`, cost `Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)`), rem
= `RemInst.hyp` (41720); inner window `KN = 41640`, frame `stkE 41640 = 43168`. The budget bounds are the box maxima
`Exp.supU` of `NBudO` / `NCost` at the LEVEL-DEPENDENT division bound `cDE` (asm s73 cost shape; no `2^16`-level
constant). The cost / need of the statement are plain `def`s (`cE`, `nE`) to keep the printed statement small.
NOT a release row (the premise is not a Janus contract): `EvenRow` = this with `hSQ` discharged, + the witness.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.EvenRow

open FvModexp.Amd64.ExpEven (NBudO cDE)

/-- `nat.rem`'s bridged cost -/
def cR : Nat → Nat → Nat → Nat := RemInst.remC
/-- `nat.expNNSlow`'s bridged cost -/
def cS : Nat → Nat → Nat → Nat → Nat :=
  Q.ExpSlow.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) Q.ExpSlow.needH
/-- `nat.expNNPowerOfTwo`'s cost -/
def cP : Nat → Nat → Nat → Nat → Nat := P2D.costP P2W2.costB P2W4.costB
/-- the inner calls' budget bound (box maximum) -/
def bUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (fun x y a l k => NBudO (cDE x a l) cR cS cP x y a l k)
/-- the inner calls' cost bound (box maximum) -/
def cUC : Nat → Nat → Nat → Nat → Nat → Nat :=
  Exp.supU (fun x y a l k => ExpN.NCost (cDE x a l) cR cS cP x y a l k)
/-- `nat.expNNEven`'s stack need -/
def nE : Nat → Nat → Nat → Nat := ExpEven.needE Q.NatRem.need ExpSlow.need P2D.needP
/-- `nat.expNNEven`'s cost -/
def cE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE bUC cUC sqrCQ mulCQ

theorem rem_mono : ∀ x a a', a ≤ a' → Q.NatRem.need x a ≤ Q.NatRem.need x a' := fun _ _ _ _ => by
  simp only [Q.NatRem.need]; omega

theorem slow_mono : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a' := fun x _ a a' h => by
  simp only [ExpSlow.need]
  by_cases h1 : x ≤ 128 ∧ a' ≤ 128
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]; exact Nat.le_refl _
  · rw [if_neg h1]; split <;> omega

theorem p2_mono : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a' := fun _ _ _ _ _ => Nat.le_refl _

theorem libW_libN : ∀ x, LibW.names.contains x = true → LibN.names.contains x = true := by
  have h : LibW.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libRem_libN : ∀ x, LibRem.names.contains x = true → LibN.names.contains x = true := by
  have h : LibRem.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libW_nfN : LibW.names.contains ExpN.fn = false := by decide +kernel
theorem libRem_nfN : LibRem.names.contains ExpN.fn = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNEven`** (amd64) as a summary on `LibNE` (frame `stkE 41640`), given `nat.expNNSlow`'s Q-form -/
theorem sumP (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {nsS : List String} {stkS : Nat}
    (hSQ : NHyp.SlowHypQ impl R nsS stkS 112 ExpSlow.need Q.ExpSlow.needH
      (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)))
    (hnsS : ∀ x, nsS.contains x = true → LibN.names.contains x = true) (hnfS : nsS.contains ExpN.fn = false)
    (hKS : stkS ≤ 41640 + 0x388) :
    ExpEven.EvenSum impl R (ExpEven.stkE 41640) 0x70 nE cE := by
  have hc : Janus.Contracts.EqHashModel.CodeIn64 (Extracted.program.ofImpl impl) (LibN.program.link impl) := by
    rw [LibN.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibN.names
  have hDN : ExpN.DHyps impl R 41640 DivInst.divC ExpSlow.need P2D.needP cS cP Q.NatDiv.names 41512 nsS stkS
      LibW.names 42520 :=
    { mkN := MakesliceLiveContract64.of_codeIn hc hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr, wb := hwb,
      div := DivInst.hyp impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub, hnsW4 := DivInst.ns_w4,
      hnsW2 := DivInst.ns_w2, hKD := by decide, slow := Q.ExpSlow.slow_of_Q hSQ, hnsS := hnsS, hnfS := hnfS,
      hKS := hKS, p2 := P2DRow.hyp impl hap R hgr hmc hmv hmk hno hwb 42520 (by decide) (by decide),
      hnsP := libW_libN, hnfP := libW_nfN, hKP := by decide }
  have hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R 41640 DivInst.divC costD Q.NatRem.need cR ExpSlow.need P2D.needP
      cS cP := fun _ =>
    ExpN.hypNE1 impl hap R hDN (RemInst.hyp impl hap R hgr hmc hwb hmk hmv hmz) libRem_libN libRem_nfN (by decide)
  exact ExpEven.fullI hap hgr hmc hmv hmz hmk hwb hE (by decide) (by decide) rem_mono slow_mono p2_mono
    (bU := bUC) (cU := cUC) (Exp.dom _) (Exp.dom _)

set_option maxRecDepth 100000 in
/-- the witness budget (`3^5 mod 6`: `xl = yl = ml = 1`, empty stack) fits the toy runtime with room to spare (asm s73:
`cE 0 1 1 1 = 318180`; the old constant-`costD` shape needed `≥ 1.1·10^7`) -/
theorem budW : cE 0 1 1 1 ≤ 0x100000 := by decide +kernel

end FvModexp.Amd64.EvenRow
