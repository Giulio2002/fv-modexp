import FvModexp.Proofs.Arm64.Exp.P2DEntP
import FvModexp.Proofs.Arm64.Exp.P2DOne
import FvModexp.Proofs.Arm64.Exp.P2DWin
import FvModexp.Proofs.Arm64.Exp.P2W2C
import FvModexp.Proofs.Arm64.Exp.P2W4C

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the odd-base summary `sumO` (agent infra)

`sumO`: a `Summary` on `LibW` at `fnE` for an ODD base `X` (no recursion): `entP`, then `logM = 1` → `oneP`;
otherwise `winR` → `winCall` with `P2W2.fullC` / `P2W4.fullC` (callee window `[SP - 112 - (stk - 112), SP - 16)`).
Generic in the window top `A` (`72 ≤ A`): the recursive call of the even case uses `A = 96`, `NHyp.P2Hyp` `A = 112`.
Budget `costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) (stLen …) lm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.EvenHyp

/-- the odd-base budget -/
@[reducible] def cO (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ lm : Nat) : Nat :=
  costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) ℓ lm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`expNNPowerOfTwo` on an odd base** (Summary on `LibW`) -/
theorem sumO {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf2 : ns.contains P2W2.fn = false)
    (hnf4 : ns.contains P2W4.fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) P2W2.grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) P2W2.mcE 4096 R)
    (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (LibW.program.link impl) P2W2.mkE 4096 R)
    (hno : NewobjectLiveContract (LibW.program.link impl) P2W2.noE 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) P2W2.wbE 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk A : Nat) (hk1 : 1072 + kcP ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 576)
    (hA : 72 ≤ A) (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (hxc : xc < 2 ^ 64) :
    Summary (LibW.program.link impl) fnE
      (fun s => Regs s zp zl zc st xp xl xc yp yl yc lm ∧
        PreD R b L stk A (cO sqC mlC (stLen s.mem st) lm) zp zl zc st xp xl yp yl lm s ∧
        natVal s.mem xp xl % 2 = 1 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => PostD R b L stk A (cO sqC mlC (stLen s.mem st) lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s') := by
  intro s hpc ⟨hR, hP, hXo, hr4, hr48⟩
  have hP' := hP
  obtain ⟨hC, hX, hY, hlm1, hlm, -, -⟩ := hP'
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hx0 : s.mem.readLE xp 8 % 2 = 1 := by
    have := val_mod2 s.mem xp xl 1 hxl0 (by omega); rw [Nat.pow_one] at this; omega
  refine entP impl _ s hP (by omega) hA hpc hR (fun hl S hS hRE hm => ?_) (fun hl _ S hS hRE hm => ?_)
    (fun _ h _ => absurd h (by omega)) (fun _ h _ => absurd h (by omega))
  · exact oneP hmk hP (by omega) hA (Nat.le_add_left _ _) hl hzp hxp hr4 hr48 S hS hRE hm
  · obtain ⟨⟨-, ⟨-, -, -, hacc⟩, -, -, -, -, -, -⟩, -, -, -, -, -, -, hins, -⟩ := hC
    obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, -⟩ := hins yp yl (by simp)
    have hyl0 : 0 < yl := by
      rcases Nat.eq_zero_or_pos yl with h | h
      · subst h; simp [natVal] at hY
      · exact h
    obtain ⟨esp, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e18, e28, e29⟩ := hRE
    have hyaW : S.mem.accessible (yp + 8 * (yl - 1)) 8 false = true := by
      rw [hm]; simp only [W0, Memory.accessible_writeLE]
      exact Memory.accessible_weaken _ (Memory.accessible_mono _ hya (by omega) (by omega))
    refine winR impl _ _ yp yl lm _ S.mem (by omega) hyn hlm hy48 hyaW rfl S hS e7 e8 e10 rfl
      fun c hc S1 h1pc h1sp h1r h18 h128 h129 h130 h1m => ?_
    have hR1 : Regs S1 zp zl zc st xp xl xc yp yl yc lm :=
      ⟨(h1r 0 (by omega)).trans e0, (h1r 1 (by omega)).trans e1, (h1r 2 (by omega)).trans e2,
        (h1r 3 (by omega)).trans e3, (h1r 4 (by omega)).trans e4, (h1r 5 (by omega)).trans e5,
        (h1r 6 (by omega)).trans e6, (h1r 7 (by omega)).trans e7, (h1r 8 (by omega)).trans e8,
        (h1r 9 (by omega)).trans e9, (h1r 10 (by omega)).trans e10⟩
    have reg : ∀ {P : State → Prop} (s1 : State), Regs s1 zp zl zc st xp xl xc yp yl yc lm ∧ P s1 →
        s1.regs 0 = BitVec.ofNat 64 zp ∧ s1.regs 1 = BitVec.ofNat 64 zl ∧ s1.regs 2 = BitVec.ofNat 64 zc ∧
        s1.regs 3 = BitVec.ofNat 64 st ∧ s1.regs 4 = BitVec.ofNat 64 xp ∧ s1.regs 5 = BitVec.ofNat 64 xl ∧
        s1.regs 6 = BitVec.ofNat 64 xc ∧ s1.regs 7 = BitVec.ofNat 64 yp ∧ s1.regs 8 = BitVec.ofNat 64 yl ∧
        s1.regs 9 = BitVec.ofNat 64 yc ∧ s1.regs 10 = BitVec.ofNat 64 lm ∧ P s1 :=
      fun _ ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, h⟩ => ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, h⟩
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact winCall (cW := fun ℓ => P2W2.cost sqC mlC ℓ lm) hP (by omega) hA hXo (by omega)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hr4 hr48
        (Summary.mono (P2W2.fullC hap hns hnf2 hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm
          htr hkT haT b L (stk - 112) (by omega) (by omega) zp zl zc st xp xl xc yp yl yc lm hzp hxc) reg (fun _ _ _ h => h))
        (Or.inl rfl) S1 h1pc (h1sp.trans esp) hR1 (h18.trans e18) (h128.trans e28) h130 (h1m.trans hm)
    · exact winCall (cW := fun ℓ => P2W4.cost sqC mlC ℓ lm) hP (by omega) hA hXo (by omega)
        (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) hr4 hr48
        (Summary.mono (P2W4.fullC hap hns hnf4 hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm
          htr hkT haT b L (stk - 112) (by omega) (by omega) zp zl zc st xp xl xc yp yl yc lm hzp hxc) reg (fun _ _ _ h => h))
        (Or.inr rfl) S1 h1pc (h1sp.trans esp) hR1 (h18.trans e18) (h128.trans e28) h130 (h1m.trans hm)

end FvModexp.Arm64.P2D
