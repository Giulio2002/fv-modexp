import FvModexp.Proofs.Arm64.Exp.SubMod2NGEns
import FvModexp.Proofs.Arm64.Exp.SubHyp0

set_option autoImplicit false

/-!
# **`nat.subMod2N`** (go-bigmodexpfix nat.go:1726), arm64 — the summary for `cap z ≥ ⌈n/64⌉` (agent infra)

`z.subMod2N(z, y, n)` (`x = z`, `y`'s array apart from `z`'s, `cap z ≥ ⌈n/64⌉`) returns a normalised nat holding
`Exp.subMod2N Z Y n` (= `(Z - Y) mod 2^n`, `ExpEven.subMod2N_correct`), in `z`'s array or a fresh one.
Derived from the general summary `fullG` / `ensG` (SubMod2NGEns; any `cap z`, empty-tolerant operands) via
`Pre.toG` / `PostG.toPost`. Callee premises: asm's `nat.trunc` (`Trunc.Hyp2`), divmc's verified empty-tolerant
`nat.sub` (`NatSub.ensR0`, through `subHypR0_of`) and `nat.add` (`NatAdd.ensR`), the live `runtime.makeslice` /
`runtime.memmove` / `runtime.growslice` contracts; `nat.cmp` is asm's verified `cmp_summary`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.EvenHyp

/-- the whole function from its entry (`Pre` form), as a `Summary` on the exp layer's program -/
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubHypR0 impl R) (hadd : AddHypR impl R)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Summary (LibW.program.link impl) 1805584
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 zp ∧ s.regs 4 = BitVec.ofNat 64 zl ∧ s.regs 5 = BitVec.ofNat 64 zc ∧
        s.regs 6 = BitVec.ofNat 64 yp ∧ s.regs 7 = BitVec.ofNat 64 yl ∧ s.regs 8 = BitVec.ofNat 64 yc ∧
        s.regs 9 = BitVec.ofNat 64 n ∧ Pre R b L op zp zl zc yp yl yc n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zl zc yp yl n s s') :=
  (fullG impl hap R hns hnf hkT haT htr hsub hadd hgr b L op zp zl zc yp yl yc n).mono
    (fun _ ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hp.toG⟩)
    (fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, hp⟩ ⟨hr, hq⟩ => ⟨hr, PostG.toPost hp.2.2.2.2.2.2.2.2.2.1 hq⟩)

def names : List String := LibW.names

/-- divmc's verified `nat.add` (`NatAdd.ensR`) is the `AddHypR` premise -/
theorem addHypR_of (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : AddHypR impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-- **`nat.subMod2N`** (arm64), `z.subMod2N(z, y, n)` with `cap z ≥ ⌈n/64⌉`: a normalised nat holding
`Exp.subMod2N Z Y n`, in `z`'s array or a fresh one; writes only `z`'s array, the window and runtime memory; no panic,
no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc, BitVec.ofNat 64 n]
      (Pre R b L op zp zl zc yp yl yc n) (Post R b L zp zl zc yp yl n) :=
  ens_of_G (ensG impl hap R hns hnf hkT haT htr (subHypR0_of impl hap R hmk hmv) hmk hmv hgr) b L op zp zl zc yp yl
    yc n

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :=
  CallWW.hypSum hap (fun _ h => h) (ens impl hap R hns hnf hkT haT htr hmk hmv hgr b L op zp zl zc yp yl yc n)

end FvModexp.Arm64.SubMod2N
