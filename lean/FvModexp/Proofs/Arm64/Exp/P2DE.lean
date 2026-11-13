import FvModexp.Proofs.Arm64.Exp.P2DFull
import FvModexp.Proofs.Arm64.Exp.P2W2E

set_option autoImplicit false

/-!
# **`nat.expNNPowerOfTwo`** (arm64): `P2D.ens : NHyp.P2Hyp …` (agent infra)

The `Ensures` form on the restricted program `LibW.names` (the caller `nat.expNN` is outside it), from the live runtime
contracts of the whole extraction and the callee summaries (`stk.nat`, `sqr`, `mul`, `trunc`, `rsh`, `lsh`) on a
program `ns ⊆ LibW.names` without `expNNPowerOfTwo` and the two windows. Window `[SP - stk, SP + 112)`, stack need
`needP` (`2^13`), budget `cP sqC mlC` (= `costP` with the window costs).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`expNNPowerOfTwo`** (arm64): `z = x^y mod 2^logM` for every positive `x`, `y` and `1 ≤ logM ≤ 2^13` -/
theorem ens {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf2 : ns.contains P2W2.fn = false)
    (hnf4 : ns.contains P2W4.fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hnf : ns.contains NHyp.fnP2 = false)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ a a', a ≤ a' → sqC a ≤ sqC a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat} (hmu : MulHypQ impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mlC a c ≤ mlC a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (haR : aboveR ≤ 88)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (haL : aboveL ≤ 88)
    (stk : Nat) (hk1 : 1184 + kcP ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 576) (hkR : stkR + 112 ≤ stk)
    (hkL : stkL + 112 ≤ stk) :
    NHyp.P2Hyp impl R LibW.names stk 112 needP (cP sqC mlC) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hgrL : GrowsliceLiveContract (LibW.program.link impl) P2W2.grE 4096 R := by
    rw [← P2W2.grE_eq]; exact fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn hc (hgr L b)
  have hmcL : MemclrNoHeapPointersLive (LibW.program.link impl) P2W2.mcE 4096 R := by
    rw [← P2W2.mcE_eq]; exact MemclrNoHeapPointersLive.of_codeIn hc hmc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have hmkL : MakesliceLiveContract (LibW.program.link impl) P2W2.mkE 4096 R := by
    rw [← P2W2.mkE_eq]; exact MakesliceLiveContract.of_codeIn hc hmk
  have hnoL : NewobjectLiveContract (LibW.program.link impl) P2W2.noE 4096 R := by
    rw [← P2W2.noE_eq]; exact NewobjectLiveContract.of_codeIn hc hno
  have hwbL : WbLiveContract (LibW.program.link impl) P2W2.wbE 4096 R 2 := by
    rw [← P2W2.wbE_eq]; exact WbLiveContract.of_codeIn hc hwb
  intro b L z zl zc st x xl xc y yl yc lm
  rw [← LibW.eq_only, fnE_eq]
  intro ret hret s hs hpre
  janus_intro hs
  have hr4 : (s.regs 30).toNat % 4 = 0 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
  have hr48 : (s.regs 30).toNat < 2 ^ 48 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega
  have bv := Expmc.bv_ofNat_toNat
  refine Summary.returns (sumF hap hns hnf2 hnf4 hnfP hnf hgrL hmcL hmvL hmkL hnoL hwbL hkc hsn hkN haN hsq hkS haS hsm
    hmu hkM haM hmm htr hkT haT hrh haR hlh haL b L stk 112 hk1 hk2 hkR hkL (by omega) z.toNat zl.toNat zc.toNat
    st.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat lm.toNat
    ⟨z.isLt, zl.isLt, zc.isLt, st.isLt, y.isLt, yl.isLt, yc.isLt, lm.isLt⟩ x.isLt xc.isLt) hret h_pc h_lr
    ⟨⟨h_x0.trans (bv _).symm, h_x1.trans (bv _).symm, h_x2.trans (bv _).symm, h_x3.trans (bv _).symm,
      h_x4.trans (bv _).symm, h_x5.trans (bv _).symm, h_x6.trans (bv _).symm, h_x7.trans (bv _).symm,
      h_x8.trans (bv _).symm, h_x9.trans (bv _).symm, h_x10.trans (bv _).symm⟩,
      hpre.1, hpre.2.1, hpre.2.2, hr4, hr48⟩
    fun s' ⟨a, b, c, d, hq⟩ => ⟨⟨a, c, d, b⟩, hq⟩

end FvModexp.Arm64.P2D
