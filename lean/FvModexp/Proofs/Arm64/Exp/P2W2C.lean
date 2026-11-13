import FvModexp.Proofs.Arm64.Exp.P2W2
import FvModexp.Proofs.Arm64.Exp.P2W2EC

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the summary in the `NHyp.CPre` form (agent infra)

`fullC`: `full` with the precondition `PreC` (window `[SP - stk, SP + 96)`, budget `cost … ≤ b` from `CPre`) and the
post `NHyp.CPostR … stk 96 …` (+ SP/R18/g/FP restored); for the `expNNPowerOfTwo` dispatch (a `Summary` on
`LibW`: its caller's return address lies inside `LibW`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem fullC {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract (LibW.program.link impl) noE 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk1 : 672 + kcP ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 464)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Summary (LibW.program.link impl) fnE
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
        s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 yp ∧ s.regs 8 = BitVec.ofNat 64 yl ∧
        s.regs 9 = BitVec.ofNat 64 yc ∧ s.regs 10 = BitVec.ofNat 64 lm ∧
        PreC R b L stk (cost sqC mlC (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧
        (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        NHyp.CPostR R b L stk 96 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
          (cost sqC mlC (stLen s.mem st) yl lm) s s') := by
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hP, hr4, hr48⟩
  have hE := epre_of hP (by omega) hk2 hzp hxc
  have hcb : cost sqC mlC (stLen s.mem st) yl lm ≤ b := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e : stk - 464 + 464 = stk := by omega
  have := full hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT haT
    b L (stk - 464) (by omega) zp zl zc st xp xl xc yp yl yc lm s hpc
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨hE, hP.2.1, hP.2.2.1, hcb⟩, hr4, hr48⟩
  simp only [FQ, e] at this
  exact this

end FvModexp.Arm64.P2W2
