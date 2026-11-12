import FvModexp.Proofs.Arm64.Exp.P2W2EP
import FvModexp.Proofs.Arm64.Exp.P2W2Cp5
import FvModexp.Proofs.Arm64.Exp.P2W2Bd
import FvModexp.Proofs.Arm64.Exp.P2W2X4

/-!
# **`nat.expNNPowerOfTwoWindowSize2`** (go-bigmodexpfix nat.go:1129-1285), arm64 — the summary (agent infra)

`z.expNNPowerOfTwoWindowSize2(stk, x, y, logM)` with `x` odd, `y > 0`, `2 ≤ logM ≤ 2^13` (and the frame/stack/object
facts `EPre`) returns a normalised nat of value `x^y mod 2^logM` (`Exp.p2win_correct`), in `z`'s array or a fresh
one (`NHyp.CPost`: live set grown, budget `cost`, `StackBackL`, frames), no panic, no fault.
Composition: `entP` (entry → reserve → `stk.nat(2w)` → table) → `afterT` (skip-zero loop, `return 1`, first window)
→ `loopKL` (body `bodyKI` = B0…B6, outer step `outerStep`, exit `exitKI`: odd-swap `z.set(zz)`, `norm`, deferred
`stk.restore`, `RET`).
Callee premises: divmc's `(*stack).nat` (`StackNat.HypL`), `nat.sqr` / `nat.mul` (`SqrHypX` / `MulHypX`), asm's
`nat.trunc` (`Trunc.Hyp2`), the live `growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`, `newobject` and
`gcWriteBarrier2` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

/-- the budget of the whole function (stack level `ℓ0` at the entry) -/
@[reducible] def cost (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ0 lm : Nat) : Nat :=
  cost0 sqC mlC ℓ0 lm + allocCost 8 + 2 * P2Pre.tC lm + 32 * ((lm - 2) / 64 + 1) * bc sqC mlC (ℓL ℓ0 lm) lm

/-- the precondition at the entry (frame `SP - 464`, `g = X28`) -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (sqC : Nat → Nat → Nat)
    (mlC : Nat → Nat → Nat → Nat) (zp zc st xp xl xc yp yl lm : Nat) (s : State) : Prop :=
  EPre R b L K (s.regs 28).toNat (s.sp.toNat - 464) st zp zc xp xl xc yp yl lm s ∧
    natVal s.mem xp xl % 2 = 1 ∧ 0 < natVal s.mem yp yl ∧ cost sqC mlC (stLen s.mem st) lm ≤ b

/-- the postcondition: the common exit shape with `ResSep` (`NHyp.CPostR`) and the value
`x^y mod 2^logM` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (sqC : Nat → Nat → Nat)
    (mlC : Nat → Nat → Nat → Nat) (zp zc st xp xl yp yl lm : Nat) (s s' : State) : Prop :=
  NHyp.CPostR R b L (K + 464) 96 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
    (cost sqC mlC (stLen s.mem st) lm) s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
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
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKk : 208 + kcP ≤ K)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) :
    Summary (LibW.program.link impl) fnE
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
        s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 yp ∧ s.regs 8 = BitVec.ofNat 64 yl ∧
        s.regs 9 = BitVec.ofNat 64 yc ∧ s.regs 10 = BitVec.ofNat 64 lm ∧
        Pre R b L K sqC mlC zp zc st xp xl xc yp yl lm s ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
        (cost sqC mlC (stLen s.mem st) lm) s s') := by
  intro s hpc hs
  obtain ⟨h0, -, h2, h3, h4, h5, h6, h7, h8, -, h10, ⟨hP, hX, hY, hbud⟩, hr4, hr48⟩ := hs
  have hmv' : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R := by rw [← P2Pre.mvE_eq]; exact hmv
  have hcb : cost sqC mlC (stLen s.mem st) lm ≤ b := hbud
  have h30 : s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine entP hap hns hnf hnfP hgr hmc hmv hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT haT
    (s.regs 30) _ b L K (s.regs 28).toNat (s.sp.toNat - 464) st zp zc xp xl xc yp yl lm (s.regs 30).toNat s hP hKk
    (by simp only [cost] at hbud; omega) hr48 hpc h0 h2 h3 h4 h5 h6 h7 h8 h10 h30 ?_
  intro s' L3 b3 zzp bp hpc' hsp' h28' h29' h18' hAT hb3
  exact afterT hap hmk hno hmv' hP hAT hb3 (by simp only [cost]; omega) hcb (by simp only [cost]; omega) hr4 hr48
    hX hY _ (fun kk => loopKL (exitKI hap hmv' hmk hP hr4 hr48 hcb) (fun i => outerStep hP i)
      (bodyKI hap hns hnf hsq (by omega) haS hsm hmu (by omega) haM hmm htr (by omega) haT hP hX hcb))
    s' hpc' hsp' h28' h29' h18' rfl

end FvModexp.Arm64.P2W2
