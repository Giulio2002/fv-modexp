import FvModexp.Proofs.Amd64.Exp.SubMod2NGS1
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS2
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS3
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS4A
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS4B
import FvModexp.Proofs.Amd64.Exp.SubMod2NGS4Cb
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# **`nat.subMod2N`** (go-bigmodexpfix nat.go:1726), amd64 — the GENERAL summary `ensG` (agent infra s49; twin of
Arm64/Exp/SubMod2NGEns.lean)

`z.subMod2N(z, y, n)` for any capacity of `z` (including `nil`) and any (possibly empty / `nil`) `y`: a normalised nat
holding `Exp.subMod2N Z Y n`, in `z`'s array or a fresh one. Callee premises: `Trunc.Hyp2` (asm), `SubHypR0` (`nat.sub`
with empty-tolerant operands; divmc's `NatSub.ensR0`), `AddHypR` (divmc's `NatAdd.ensR`), the live `growslice`
contract (the `append` loop); `nat.cmp` is asm's verified `cmp_summary`. `n` is the tenth argument, on the stack
(`PreG`'s `Ent` conjunct).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

/-- the whole function from its entry (general form), as a `Summary` on `LibW` -/
theorem fullG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubHypR0 impl R) (hadd : AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Summary (LibW.program.link impl) 6215840
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
        s.regs 7 = BitVec.ofNat 64 zp ∧ s.regs 6 = BitVec.ofNat 64 zl ∧ s.regs 8 = BitVec.ofNat 64 zc ∧
        s.regs 9 = BitVec.ofNat 64 yp ∧ s.regs 10 = BitVec.ofNat 64 yl ∧ s.regs 11 = BitVec.ofNat 64 yc ∧
        PreG R b L op zp zl zc yp yl yc n s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ PostG R b L zp zl zc yp yl n s s') := by
  intro s hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have k5 := s4cG impl hap R hns hnf hkT haT htr hadd b L op zp zl zc yp yl yc n s
  have k4 := s4bG impl R b L op zp zl zc yp yl yc n s k5
  have k3 := s4aG impl R hgr b L op zp zl zc yp yl yc n s k4
  have k2 := s3G impl hap R hsub b L op zp zl zc yp yl yc n s k3
  have k1 := s2G impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s k2
  exact s1G impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre k1

/-- a growslice contract on a larger program restricts to one containing its code (as divmc's
`GrowsliceLiveContract64.of_codeIn'`, Amd64/Nat/StackNatX.lean) -/
theorem growslice_of_codeIn {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : GrowsliceLiveContract64 p a st R) : GrowsliceLiveContract64 P a st R :=
  fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (h L b)

/-- **`nat.subMod2N`** (amd64), general form: `EnsG` from the callee premises -/
theorem ensG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R) :
    EnsG impl R := by
  intro b L op zp zl zc yp yl yc n
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only, show segAddr Extracted.program fn = 6215840 by decide]
  janus64_ensures_old [FvModexp.Amd64.SubMod2N.PreG, FvModexp.Amd64.CallEnv, FvModexp.Amd64.SubMod2N.K, FvModexp.Amd64.SubMod2N.A, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.NatLive, FvModexp.Amd64.SubMod2N.Ent, FvModexp.Amd64.TlsOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (fullG impl hap R hns hnf hkT haT htr (subHypR0_of impl hap R hmk hmv)
    (fun b L zp zl zc xp xl xc yp yl yc => NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc)
    (growslice_of_codeIn hc hgr) b L op zp zl zc yp yl yc n) hret
    (by rw [h_rip]) (by rw [retAddrOf, h_ret])
    ⟨h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7, h_a8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ensG` as a callee summary in a caller whose program keeps `LibW.names` -/
def sumG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :=
  hypSumW hap (fun _ h => h) (by simp [numIntRegs])
    (ensG impl hap R hns hnf hkT haT htr hmk hmv hgr b L op zp zl zc yp yl yc n)

/-- the old `Pre`/`Post` statement (for a `z` with `cap z ≥ ⌈n/64⌉`) from `ensG`, on `LibW` -/
theorem ens_of_G {impl : List Amd64.Segment} {R : RtInv} (h : EnsG impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc]
      (Pre R b L op zp zl zc yp yl yc n) (Post R b L zp zl zc yp yl n) :=
  (h b L op zp zl zc yp yl yc n).mono_ret (fun _ hp => hp.toG)
    (fun _ _ _ hp hq => PostG.toPost hp.2.2.2.2.2.2.2.2.2.1 hq)

end FvModexp.Amd64.SubMod2N
