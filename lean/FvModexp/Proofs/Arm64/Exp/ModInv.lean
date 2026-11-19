import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.ModInvEntry
import FvModexp.Proofs.Arm64.Exp.ModInvSmall
import FvModexp.Proofs.Arm64.Exp.ModInvMake
import FvModexp.Proofs.Arm64.Exp.ModInvMkZZ
import FvModexp.Proofs.Arm64.Exp.ModInvLoop
import FvModexp.Proofs.Arm64.Exp.ModInvQDefs

set_option autoImplicit false

/-!
# **`nat.modularInverseModPowerOfTwo`** (go-bigmodexpfix nat.go:1287-1341), arm64 — the summary (agent infra)

`z.modularInverseModPowerOfTwo(stk, x, n)` (`x` normalised and odd, `1 ≤ n ≤ 2^15`, `cap z > 0`, `z` apart from `x`)
returns a normalised nat holding `Exp.modularInverseModPowerOfTwo X n` (`x⁻¹ mod 2^n`), in `z`'s array or a fresh one.
Paths: `n ≤ 64` (`ModInvSmall`), else `z.make`/`zz.make` (`make`, `mkzz`) and the Hensel loop (`loop`).
Callee premises: `nat.sqr` / `nat.mul` in Q-form (`SqrHypQ` / `MulHypQ`, divmc; level-free costs `sqrC` / `mulC`),
asm's `nat.trunc` / `nat.lsh` (`Trunc.Hyp2`, `Lsh.Hyp2`), `nat.subMod2N` (verified; `Trunc.Hyp2` / `SubHypR0` /
`AddHypR` / growslice premises), the live `runtime.makeslice` contract.
TIGHT COSTS (infra s44/s45): round `j` charged at its actual sizes (`roundCost`), ONE reserve level `H` per call:
`ensQ` (Q-form: `PreQ`/`PostQ`, `H` ∀ before the budget) and the bridged level-cost form `ens` (`PreL`/`PostL`,
`H := ℓ + D n`, cost `cost + stkRes (ℓ + D n)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program (internal budget form: `b` is the
budget left after the reserve, `R.inv (b + stkR H s.mem st)`) -/
theorem full {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqrC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mulC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mulC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (H b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Summary (LibW.program.link impl) 1797104
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
        s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 n ∧
        Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R kc H sqrC mulC b L zp zc st xp xl n s s') := by
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, hpre⟩
  have kL : J2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s :=
    loop hap hns hnf hnfS hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4 hsub hadd hgr hsm hmm
  exact entry impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s hkc hpc h0 h1 h2 h3 h4 h5 h6 h7 hpre
    (small impl R hmk kc H _ _ b L zp zl zc st xp xl xc n s hkc)
    (make impl R hmk kc H _ _ b L zp zl zc st xp xl xc n s hkc
      (mkzz impl R hmk kc H _ _ b L zp zl zc st xp xl xc n s hkc kL))

def names : List String := LibW.names

set_option maxRecDepth 20000 in
/-- **`nat.modularInverseModPowerOfTwo`** (arm64), Q-form: `z.modularInverseModPowerOfTwo(stk, x, n)` returns a
normalised nat holding `x⁻¹ mod 2^n` (`Exp.modularInverseModPowerOfTwo`), in `z`'s array or a fresh one; writes only
`z`'s array, the window, the stack object's writable parts and runtime memory; no panic, no fault. Budget: one reserve
level `H ≥ stLen + D n`, cost `cost sqrC mulC xl n + stkR H s.mem st`, refund `stkR H s'.mem st`. -/
theorem ensQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqrC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mulC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mulC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (H B : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (PreQ R kc H sqrC mulC B L zp zl zc st xp xl xc n) (PostQ R kc H sqrC mulC B L zp zc st xp xl n) := by
  janus_ensures_old [FvModexp.Arm64.ModInv.PreQ, FvModexp.Exp.B, FvModexp.Arm64.CallEnv, FvModexp.Arm64.ModInv.A, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.winA, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.ExpHyp.stWs, FvModexp.Arm64.ExpHyp.WrOut, FvModexp.Arm64.ExpHyp.RdIn, FvModexp.NatNorm, FvModexp.natVal, FvModexp.Arm64.EvenHyp.StkIn, FvModexp.stLen, FvModexp.Arm64.EvenHyp.StkApart, FvModexp.stkR, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.ModInv.OneIn, FvModexp.Arm64.ModInv.PX, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.win, FvModexp.Arm64.RunIface.wbA, FvModexp.stkWs, FvModexp.Asm.top, FvModexp.NatLive, FvModexp.Arm64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stkRes, FvModexp.potK, FvModexp.Arm64.EvenHyp.NatOne, FvModexp.Arm64.EvenHyp.natOneA, FvModexp.Arm64.StackNat.wbA, FvModexp.Arm64.EvenHyp.frP, FvModexp.Arm64.EvenHyp.frN, FvModexp.Arm64.EvenHyp.OpX, FvModexp.StkOK]
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract.of_codeIn hc hmk
  have hgrL : GrowsliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R :=
    fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn hc (hgr L b)
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = 1797104 by decide]
  intro ret hret s hs hpre
  janus_intro hs
  refine Summary.returns (full hap hns hnf hnfS hmkL hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4
    hsub hadd hgrL hsm hmm H (B - stkR H s.mem st) L zp zl zc st xp xl xc n) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, pre_of_Q hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, post_of_Q hq⟩

set_option maxRecDepth 20000 in
/-- **`nat.modularInverseModPowerOfTwo`** (arm64), the bridged level-cost form (`H := ℓ + D n` at the entry stack length
`ℓ`): cost `cost sqrC mulC xl n + stkRes (ℓ + D n)` -/
theorem ens {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqrC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mulC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mulC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (PreL R kc sqrC mulC ℓ b L zp zl zc st xp xl xc n) (PostL R kc sqrC mulC ℓ b L zp zc st xp xl n) :=
  (ensQ hap hns hnf hnfS hmk hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4 hsub hadd hgr hsm hmm (ℓ + D n) b L zp zl zc st xp xl xc n).mono_ret
    (fun _ h => h.1) (fun _ _ _ _ h => postL_of_Q h)

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfS : ns.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkS aboveS : Nat} {sqrC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {stkM aboveM : Nat} {mulC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mulC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hkT4 : stkT ≤ 4464)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :=
  CallWW.hypSum hap (fun _ h => h) (ens hap hns hnf hnfS hmk hkc hsq hkS haS htr hkT haT hmu hkM haM hls hkL haL hkT4 hsub hadd hgr hsm hmm ℓ b L zp zl zc st xp xl xc n)

end FvModexp.Arm64.ModInv
