import FvModexp.Proofs.Arm64.Exp.SubMod2NGS1
import FvModexp.Proofs.Arm64.Exp.SubMod2NGS2
import FvModexp.Proofs.Arm64.Exp.SubMod2NGS3b
import FvModexp.Proofs.Arm64.Exp.SubMod2NGS4A
import FvModexp.Proofs.Arm64.Exp.SubMod2NGS4B
import FvModexp.Proofs.Arm64.Exp.SubMod2NGS4Cb
import Janus.Contracts.InternalCall

set_option autoImplicit false

/-!
# **`nat.subMod2N`** (go-bigmodexpfix nat.go:1726), arm64 — the GENERAL summary `ensG` (agent infra)

`z.subMod2N(z, y, n)` for any capacity of `z` (including `nil`) and any (possibly empty / `nil`) `y`: a normalised nat
holding `Exp.subMod2N Z Y n`, in `z`'s array or a fresh one. Callee premises: `Trunc.Hyp2` (asm), `SubHypR0` (`nat.sub`
with empty-tolerant operands; divmc), `AddHypR` (divmc's `NatAdd.ensR`), the live `growslice` contract (the `append`
loop); `nat.cmp` is asm's verified `cmp_summary`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.EvenHyp Janus.Contracts.EqHashModel

/-- the whole function from its entry (general form), as a `Summary` on the exp layer's program -/
theorem fullG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubHypR0 impl R) (hadd : AddHypR impl R)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Summary (LibW.program.link impl) 1805584
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 zp ∧ s.regs 4 = BitVec.ofNat 64 zl ∧ s.regs 5 = BitVec.ofNat 64 zc ∧
        s.regs 6 = BitVec.ofNat 64 yp ∧ s.regs 7 = BitVec.ofNat 64 yl ∧ s.regs 8 = BitVec.ofNat 64 yc ∧
        s.regs 9 = BitVec.ofNat 64 n ∧ PreG R b L op zp zl zc yp yl yc n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostG R b L zp zl zc yp yl n s s') := by
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpre⟩
  have k5 := s4cG impl hap R hns hnf hkT haT htr hadd b L op zp zl zc yp yl yc n s
  have k4 := s4bG impl R b L op zp zl zc yp yl yc n s k5
  have k3 := s4aG impl R hgr b L op zp zl zc yp yl yc n s k4
  have k2 := s3G impl hap R hsub b L op zp zl zc yp yl yc n s k3
  have k1 := s2G impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s k2
  exact s1G impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre k1

/-- **`nat.subMod2N`** (arm64), general form: `EnsG` from the callee premises -/
theorem ensG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubHypR0 impl R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R) :
    EnsG impl R := by
  intro b L op zp zl zc yp yl yc n
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibW.names
  have hgr' : GrowsliceLiveContract (LibW.program.link impl) (cA "runtime.growslice") 4096 R :=
    fun L b => EqHashModel.Summary.of_codeIn hc (hgr L b)
  rw [← LibW.eq_only, show segAddr Extracted.program fn = 1805584 by decide]
  janus_ensures_old [FvModexp.Arm64.SubMod2N.PreG, FvModexp.Arm64.CallEnv, FvModexp.Arm64.SubMod2N.K, FvModexp.Arm64.SubMod2N.A, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.EvenHyp.NatOne, FvModexp.Arm64.win, FvModexp.Arm64.EvenHyp.natOneA, FvModexp.NatLive, FvModexp.NatNorm, FvModexp.Arm64.SubMod2N.costG, Janus.Spec.GuardOK, Janus.Spec.StackOK]
  intro ret hret s hs hpre
  janus_intro hs
  refine Summary.returns (fullG impl hap R hns hnf hkT haT htr hsub (fun b L zp zl zc xp xl xc yp yl yc => NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hgr' b L op zp zl
    zc yp yl yc n) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ensG` as a callee summary in a caller whose program keeps `LibW.names` -/
def sumG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubHypR0 impl R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :=
  CallWW.hypSum hap (fun _ h => h) (ensG impl hap R hns hnf hkT haT htr hsub hmk hmv hgr b L op zp zl zc yp yl yc n)

/-- the old `SubHypR`-free `ens` statement from `ensG` (for a `z` with `cap z ≥ ⌈n/64⌉`), once `SubHypR0` is
available -/
theorem ens_of_G {impl : List Segment} {R : RtInv} (h : EnsG impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (Pre R b L op zp zl zc yp yl yc n) (Post R b L zp zl zc yp yl n) :=
  (h b L op zp zl zc yp yl yc n).mono_ret (fun _ hp => hp.toG)
    (fun _ _ _ hp hq => PostG.toPost hp.2.2.2.2.2.2.2.2.2.1 hq)

end FvModexp.Arm64.SubMod2N
