import FvModexp.Proofs.Arm64.Exp.IExpCl
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# Row: `nat.expNNEven` (arm64) on the Run extraction (agent infra)

`correctness` = `ExpEven.fullI` (the CRT split `m = 2^n · m2`: two inner `nat.expNN` calls, `subMod2N`,
`modularInverseModPowerOfTwo`, two `mul`s, `trunc`, `add`) with EVERY callee proved: the inner `nat.expNN` is expmc's
`ExpN.ens_noEven` (window 70720) on the closed callee shapes `IExp.dhyps` (asm's `nat.div`, expmc's `expNNSlow`, infra's
`expNNPowerOfTwo`) and asm's `NatRem.ensC`; the cost bounds `bU`/`cU` are the dominating box maxima `Exp.supU` (expmc's
`Common/NCostU`, as top's `Run.Closed.expC`); the need monotonicity facts are proved here (copied from top's RunOkRowC).
Window `[SP - 72368, SP + 112)`. Runtime premises: the live `makeslice`, `growslice`, `memclrNoHeapPointers`,
`memmove` (+ zero-length), `newobject`, `gcWriteBarrier2` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenRow

abbrev cF : Nat → Nat → Nat → Nat := NatDiv.cost DivRec.drsC
abbrev cR : Nat → Nat → Nat → Nat := NatRem.cost cF
abbrev cS : Nat → Nat → Nat → Nat → Nat := ExpSlow.cost sqrC mulC cF
abbrev cP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrC mulC
abbrev bUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE cF cR cS cP)
abbrev cUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost cF cR cS cP)
/-- `nat.expNNEven`'s stack need and cost -/
abbrev nE : Nat → Nat → Nat → Nat := ExpEven.needE NatRem.need ExpSlow.need P2D.needP
abbrev cE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE cF cR cS cP bUC cUC sqrCQ mulCQ mulC

/-- (copied from top's `Run.Closed.rem_mono`) -/
theorem rem_mono : ∀ x a a', a ≤ a' → NatRem.need x a ≤ NatRem.need x a' := fun _ _ _ _ => by
  simp only [NatRem.need]; omega

/-- (copied from top's `Run.Closed.slow_mono`) -/
theorem slow_mono : ∀ x y a a', a ≤ a' → ExpSlow.need x y a ≤ ExpSlow.need x y a' := fun x _ a a' h => by
  simp only [ExpSlow.need]
  by_cases h1 : x ≤ 128 ∧ a' ≤ 128
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]; exact Nat.le_refl _
  · rw [if_neg h1]; split <;> omega

theorem p2_mono : ∀ x y a a', a ≤ a' → P2D.needP x y a ≤ P2D.needP x y a' := fun _ _ _ _ _ => Nat.le_refl _

theorem fnE_eq : segAddr Extracted.program ExpEven.fn = ExpEven.fnE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.expNNEven` as a closed summary on `LibNE` (window 72368) -/
theorem sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ExpEven.EvenSum impl R 72368 112 nE cE := by
  have hDN := IExp.dhyps hap hmk hgr hmc hmv hmz hno hwb (K := 70720) (Nat.le_refl _)
  have hRem : NHyp.RemHyp impl R LibRem.names 41712 112 NatRem.need cR :=
    NatRem.ensC impl hap R hgr hmc hwb hmk hmv hmz
  have hNE : EvenHyp.ExpNNHypNE impl R 70720 cF NatRem.need cR ExpSlow.need P2D.needP cS cP :=
    fun b L zp zl zc st xp xl xc yp yl yc mp n mc slow =>
      ExpN.ens_noEven impl hap R hDN hRem IExp.rem_n IExp.rem_11 (by decide) b L zp zl zc st xp xl xc yp yl yc mp n
        mc slow
  exact ExpEven.fullI hap hmk hgr hmc hmv hmz hwb (EvenHyp.ExpNNHypNE.toNE1 hNE) (by decide) (by decide)
    rem_mono slow_mono p2_mono (bU := bUC) (cU := cUC) (Exp.dom _) (Exp.dom _) (stk := 72368) (by decide) (by decide)
    (by decide)

/-- the precondition (= `EvenSum`'s, window `72368`/`112`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl m ml mc : Nat)
    (s : State) : Prop :=
  ExpEven.Pre R b L 72368 112 nE cE z zl zc st x xl y yl m ml mc s ∧ NHyp.XFacts R L x xl xc

/-- the postcondition: the ABI registers kept and `CPostR` with the value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z zc st x xl y yl m ml : Nat) (s s' : State) :
    Prop :=
  ExpEven.Post R b L 72368 112 cE z zc st x xl y yl m ml s s'

set_option maxHeartbeats 64000000 in
/-- **`nat.expNNEven`** (arm64): `z.expNNEven(stk, x, y, m)` returns `x^y mod m` for every `x > 0`, `y ≥ 2`, even
`m > 0` of at most 128 words (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear /
write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpEven.fn)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]
      (Pre R b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat m.toNat ml.toNat
        mc.toNat)
      (Post R b L z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat ml.toNat) := by
  have hS := sum impl hap R hmk hgr hmc hmv hmz hno hwb
  refine Ensures.full (ns := LibNE.names) hap ?_
  rw [← LibNE.eq_only, fnE_eq]
  intro ret hret s hs hpre
  janus_intro hs
  have hr4 : (s.regs 30).toNat % 4 = 0 := by
    rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
  have hr48 : (s.regs 30).toNat < 2 ^ 48 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega
  have bv := Expmc.bv_ofNat_toNat
  exact Summary.returns (hS b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat
      yc.toNat m.toNat ml.toNat mc.toNat) hret h_pc h_lr
    ⟨h_x0.trans (bv _).symm, h_x1.trans (bv _).symm, h_x2.trans (bv _).symm, h_x3.trans (bv _).symm,
      h_x4.trans (bv _).symm, h_x5.trans (bv _).symm, h_x6.trans (bv _).symm, h_x7.trans (bv _).symm,
      h_x8.trans (bv _).symm, h_x9.trans (bv _).symm, h_x10.trans (bv _).symm, h_x11.trans (bv _).symm,
      h_x12.trans (bv _).symm, hpre.1, z.isLt, xc.isLt, yc.isLt, hr4, hr48, hpre.2⟩
    fun s' hq => ⟨⟨hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.1⟩, hq⟩

end FvModexp.Arm64.EvenRow

