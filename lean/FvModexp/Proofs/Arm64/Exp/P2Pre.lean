import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.P2PreE
import FvModexp.Proofs.Arm64.Exp.P2PreX1
import FvModexp.Proofs.Arm64.Exp.P2PreXT
import FvModexp.Proofs.Arm64.Exp.P2PreLoop

set_option autoImplicit false

/-!
# **`buildPrecomputationWindowModPower2`** (go-bigmodexpfix nat.go:856-899), arm64 — the summary (agent infra)

`buildPrecomputationWindowModPower2(stk, powers, windowSize, logM, x)` with `windowSize ∈ {2, 4}`,
`len(powers) = 2^windowSize`, `2 ≤ logM ≤ 2^13`, `x` normalised: every `powers[j]` (`j < len`) is a normalised nat of at
most `w = ⌈logM/64⌉` words holding `Exp.p2Pow logM X j` (`= X^j mod 2^logM`), stored in the scratch nat
`buf = stk.nat((len+1) w)` at `buf + 8 j w` (cap `w`); the stack grows by `rnd((len+1) w)` words; only `powers`, the
stack object's writable parts, the window and runtime memory are written; no panic, no fault.
Composition: `segE` (entry → `stk.nat` → `FillJ 0`), `fill_all` (fill loop), `exitF` (`powers[0] = 1`), `jX1`
(`trunc(x)`), `segT` (→ `HeadJ 2`), `head_all` (main loop, return).
Callee premises: divmc's `(*stack).nat` (`StackNat.Hyp`), `nat.sqr` / `nat.mul` (`SqrHypR` / `MulHypR`), asm's
`nat.trunc` (`Trunc.Hyp2`), the live `runtime.memmove` and `runtime.gcWriteBarrier2` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88) (hsm : ∀ a a', a ≤ a' → sqC a ≤ sqC a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mlC a c ≤ mlC a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :
    Summary (LibW.program.link impl) 1790928
      (fun s => s.regs 0 = BitVec.ofNat 64 st ∧ s.regs 1 = BitVec.ofNat 64 pw ∧ s.regs 2 = BitVec.ofNat 64 pl ∧
        s.regs 3 = BitVec.ofNat 64 pc ∧ s.regs 4 = BitVec.ofNat 64 ws ∧ s.regs 5 = BitVec.ofNat 64 lm ∧
        s.regs 6 = BitVec.ofNat 64 x ∧ s.regs 7 = BitVec.ofNat 64 xl ∧ s.regs 8 = BitVec.ofNat 64 xc ∧
        Pre R kc sqC mlC b L st pw pl ws lm x xl s)
      (fun s s' => GoalQ R kc sqC mlC b L st pw pl lm x xl s s') := by
  intro s hpc hs
  obtain ⟨h0, h1, h2, -, h4, h5, h6, h7, -, hpre⟩ := hs
  have hx := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx6 : (s.regs 6).toNat = x := by rw [h6, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hx.2.2.1; omega)
  have hx7 : (s.regs 7).toNat = xl := by rw [h7, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hx.1; omega)
  have hpl := pl_facts hpre
  exact segE hap hns hnf hsn hkN haN hkc hpre hpc h0 h1 h2 h4 h5
    (fill_all hwb hkc hpre (exitF hmv hwb hkc hpre (jX1 hap hns hnf htr hkT haT hkc hpre hx6 hx7
      (segT hwb hkc hpre (head_all hap hns hnf hsq hkS haS hsm hmu hkM haM hmm htr hkT haT hwb hkc hpre (pl - 2) 2 rfl
        (by decide) (Nat.le_refl _) (by omega))))) pl 0 (by omega))

def names : List String := LibW.names

set_option maxRecDepth 20000 in
/-- **`buildPrecomputationWindowModPower2`** (arm64): the table `powers[j] = X^j mod 2^logM` (`Exp.p2Pow`), see the
module doc; `Post` (P2PreDefs) states the values, the stack growth, the scratch nat and the frames. -/
theorem ens {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88) (hsm : ∀ a a', a ≤ a' → sqC a ≤ sqC a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mlC a c ≤ mlC a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 st, BitVec.ofNat 64 pw, BitVec.ofNat 64 pl, BitVec.ofNat 64 pc, BitVec.ofNat 64 ws,
        BitVec.ofNat 64 lm, BitVec.ofNat 64 x, BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (Pre R kc sqC mlC b L st pw pl ws lm x xl) (Post R kc sqC mlC b L st pw pl lm x xl) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have hwbL : WbLiveContract (LibW.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract.of_codeIn hc hwb
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = 1790928 by decide]
  intro ret hret s hs hpre
  janus_intro hs
  refine Summary.returns (full hap hns hnf hmvL hwbL hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT haT
    b L st pw pl pc ws lm x xl xc) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibW.names` -/
def sum {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kc) (haS : aboveS ≤ 88) (hsm : ∀ a a', a ≤ a' → sqC a ≤ sqC a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mlC a c ≤ mlC a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :=
  CallWW.hypSum hap (fun _ h => h) (ens hap hns hnf hmv hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT
    haT b L st pw pl pc ws lm x xl xc)

end FvModexp.Arm64.P2Pre
