import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.ModInvEntry
import FvModexp.Proofs.Arm64.Exp.ModInvSmall
import FvModexp.Proofs.Arm64.Exp.ModInvMake
import FvModexp.Proofs.Arm64.Exp.ModInvMkZZ
import FvModexp.Proofs.Arm64.Exp.ModInvLoop

/-!
# **`nat.modularInverseModPowerOfTwo`** (go-bigmodexpfix nat.go:1287-1341), arm64 — the summary (agent infra)

`z.modularInverseModPowerOfTwo(stk, x, n)` (`x` normalised and odd, `1 ≤ n ≤ 2^15`, `cap z > 0`, `z` apart from `x`)
returns a normalised nat holding `Exp.modularInverseModPowerOfTwo X n` (`x⁻¹ mod 2^n`), in `z`'s array or a fresh one.
Paths: `n ≤ 64` (`ModInvSmall`), else `z.make`/`zz.make` (`make`, `mkzz`) and the Hensel loop (`loop`).
Callee premises: `nat.sqr` / `nat.mul` (`SqrHyp` / `MulHyp`, divmc), asm's `nat.trunc` / `nat.lsh` (`Trunc.Hyp2`,
`Lsh.Hyp2`), `nat.subMod2N` (verified; `Trunc.Hyp2` / `SubHypR0` / `AddHypR` / growslice premises), the live
`runtime.makeslice` contract. The budgets of `sqr` / `mul` depend on the stack length `ℓ` at entry (`stLen s.mem st = ℓ`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Summary (LibW.program.link impl) 1797104
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
        s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 n ∧
        PreL R kc sqC mlC ℓ b L zp zl zc st xp xl xc n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R kc (sqC ℓ) (mlC ℓ) b L zp zc st xp xl n s s') := by
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, hpre, hℓ⟩
  have kL : J2 impl R kc (sqC ℓ) (mlC ℓ) b L zp zl zc st xp xl xc n s := loop hap hns hnf hnfS hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4 hsub hadd hgr
    (fun x => by rw [hℓ]) (hsm ℓ) (fun x y => by rw [hℓ]) (hmm ℓ)
  exact entry impl R kc (sqC ℓ) (mlC ℓ) b L zp zl zc st xp xl xc n s hkc hpc h0 h1 h2 h3 h4 h5 h6 h7 hpre
    (small impl R hmk kc _ _ b L zp zl zc st xp xl xc n s hkc)
    (make impl R hmk kc _ _ b L zp zl zc st xp xl xc n s hkc (mkzz impl R hmk kc _ _ b L zp zl zc st xp xl xc n s hkc kL))

def names : List String := LibW.names

set_option maxRecDepth 20000 in
/-- **`nat.modularInverseModPowerOfTwo`** (arm64), `z.modularInverseModPowerOfTwo(stk, x, n)`: a normalised nat
holding `x⁻¹ mod 2^n` (`Exp.modularInverseModPowerOfTwo`), in `z`'s array or a fresh one; writes only `z`'s array, the
window, the stack object's writable parts and runtime memory; no panic, no fault. -/
theorem ens {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (PreL R kc sqC mlC ℓ b L zp zl zc st xp xl xc n) (Post R kc (sqC ℓ) (mlC ℓ) b L zp zc st xp xl n) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract.of_codeIn hc hmk
  have hgrL : GrowsliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R :=
    fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn hc (hgr L b)
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = 1797104 by decide]
  intro ret hret s hs hpre
  janus_intro hs
  refine Summary.returns (full hap hns hnf hnfS hmkL hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4
    hsub hadd hgrL hsm hmm ℓ b L zp zl zc st xp xl xc n) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat)  :=
  CallWW.hypSum hap (fun _ h => h) (ens hap hns hnf hnfS hmk hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4
    hsub hadd hgr hsm hmm ℓ b L zp zl zc st xp xl xc n)

end FvModexp.Arm64.ModInv
