import FvModexp.Proofs.Arm64.Exp.P2W2

/-!
# **`nat.expNNPowerOfTwoWindowSize2`** (arm64): `ens` / `sum` (agent infra)

`ens`: the `Ensures` form on the restricted program `LibExp.names` (callers outside it), from the live runtime
contracts of the whole extraction; `sum`: `ens` as a callee summary (`CallW.hypSum`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

def names : List String := LibExp.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`expNNPowerOfTwoWindowSize2`** (arm64): returns `x^y mod 2^logM` for odd `x`, `y > 0` (see `Pre`/`Post`) -/
theorem ens {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKk : 208 + kcP ≤ K)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 lm]
      (Pre R b L K sqC mlC zp zc st xp xl xc yp yl lm) (Post R b L K sqC mlC zp zc st xp xl yp yl lm) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibExp.names
  rw [← LibExp.eq_only] at hc
  have hgrL : GrowsliceLiveContract (LibExp.program.link impl) grE 4096 R := by
    rw [← grE_eq]; exact fun L b => Janus.Contracts.EqHashModel.Summary.of_codeIn hc (hgr L b)
  have hmcL : MemclrNoHeapPointersLive (LibExp.program.link impl) mcE 4096 R := by
    rw [← mcE_eq]; exact MemclrNoHeapPointersLive.of_codeIn hc hmc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have hmkL : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R := by
    rw [← mkE_eq]; exact MakesliceLiveContract.of_codeIn hc hmk
  have hnoL : NewobjectLiveContract (LibExp.program.link impl) noE 4096 R := by
    rw [← noE_eq]; exact NewobjectLiveContract.of_codeIn hc hno
  have hwbL : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2 := by
    rw [← wbE_eq]; exact WbLiveContract.of_codeIn hc hwb
  rw [show names = LibExp.names from rfl, ← LibExp.eq_only, show segAddr Extracted.program fn = fnE by decide]
  intro ret hret s hs hpre
  janus_intro hs
  have hr4 : (s.regs 30).toNat % 4 = 0 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
  have hr48 : (s.regs 30).toNat < 2 ^ 48 := by rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega
  refine Summary.returns (full hap hns hnf hnfP hgrL hmcL hmvL hmkL hnoL hwbL hkc hsn hkN haN hsq hkS haS hsm hmu hkM
    haM hmm htr hkT haT b L K hKk zp zl zc st xp xl xc yp yl yc lm) hret h_pc h_lr
    ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9, h_x10, hpre, hr4, hr48⟩
    fun s' ⟨a, b, c, d, hq⟩ => ⟨⟨a, c, d, b⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibExp.names` -/
def sum {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKk : 208 + kcP ≤ K)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) :=
  CallW.hypSum hap (fun _ h => h) (ens hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS haS hsm hmu
    hkM haM hmm htr hkT haT b L K hKk zp zl zc st xp xl xc yp yl yc lm)

end FvModexp.Arm64.P2W2
