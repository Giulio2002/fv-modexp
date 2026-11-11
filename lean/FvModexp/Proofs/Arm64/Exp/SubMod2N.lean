import FvModexp.Proofs.Arm64.Exp.SubMod2NS1
import FvModexp.Proofs.Arm64.Exp.SubMod2NS2
import FvModexp.Proofs.Arm64.Exp.SubMod2NS3
import FvModexp.Proofs.Arm64.Exp.SubMod2NS4B
import FvModexp.Proofs.Arm64.Exp.SubMod2NS4C
import FvModexp.Proofs.Arm64.Nat.NatSub
import FvModexp.Proofs.Arm64.Nat.NatAdd

/-!
# **`nat.subMod2N`** (go-bigmodexpfix nat.go:1726), arm64 — the summary (agent infra)

`z.subMod2N(z, y, n)` (`x = z`, `y`'s array apart from `z`'s, `cap z ≥ ⌈n/64⌉`) returns a normalised nat holding
`Exp.subMod2N Z Y n` (= `(Z - Y) mod 2^n`, `ExpEven.subMod2N_correct`), in `z`'s array or a fresh one. Callee premises:
`TruncHyp` (asm's `nat.trunc`, not landed), and the live `runtime.makeslice` / `runtime.memmove` contracts used by divmc's
verified `nat.sub` / `nat.add` (`NatSub.ensR` / `NatAdd.ensR` discharge `SubHypR` / `AddHypR`); `nat.cmp` is asm's
verified `cmp_summary`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.EvenHyp

/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : TruncHyp impl R ns stkT aboveT)
    (hsub : SubHypR impl R) (hadd : AddHypR impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Summary (LibExp.program.link impl) 1805584
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 zp ∧ s.regs 4 = BitVec.ofNat 64 zl ∧ s.regs 5 = BitVec.ofNat 64 zc ∧
        s.regs 6 = BitVec.ofNat 64 yp ∧ s.regs 7 = BitVec.ofNat 64 yl ∧ s.regs 8 = BitVec.ofNat 64 yc ∧
        s.regs 9 = BitVec.ofNat 64 n ∧ Pre R b L op zp zl zc yp yl yc n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zl zc yp yl n s s') := by
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpre⟩
  have k5 := s4c impl hap R hns hnf hkT haT htr hadd b L op zp zl zc yp yl yc n s
  have k4 := s4b impl R b L op zp zl zc yp yl yc n s k5
  have k3 := s4a impl R b L op zp zl zc yp yl yc n s k4
  have k2 := s3 impl hap R hsub b L op zp zl zc yp yl yc n s k3
  have k1 := s2 impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s k2
  exact s1 impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre k1

def names : List String := LibExp.names

/-- divmc's verified `nat.sub` (`NatSub.ensR`) is the `SubHypR` premise -/
theorem subHypR_of (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : SubHypR impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatSub.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-- divmc's verified `nat.add` (`NatAdd.ensR`) is the `AddHypR` premise -/
theorem addHypR_of (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : AddHypR impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-- **`nat.subMod2N`** (arm64), `z.subMod2N(z, y, n)`: a normalised nat holding `Exp.subMod2N Z Y n`, in `z`'s array
or a fresh one; writes only `z`'s array, the window and runtime memory; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : TruncHyp impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (Pre R b L op zp zl zc yp yl yc n) (Post R b L zp zl zc yp yl n) := by
  rw [show names = LibExp.names from rfl, ← LibExp.eq_only, show segAddr Extracted.program fn = 1805584 by decide]
  intro ret hret s hs hpre
  janus_intro hs
  refine Summary.returns (full impl hap R hns hnf hkT haT htr (subHypR_of impl hap R hmk hmv)
    (addHypR_of impl hap R hmk hmv) b L op zp zl zc yp yl yc n) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibExp.names` -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : TruncHyp impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :=
  CallW.hypSum hap (fun _ h => h) (ens impl hap R hns hnf hkT haT htr hmk hmv b L op zp zl zc yp yl yc n)

end FvModexp.Arm64.SubMod2N
