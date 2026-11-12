import FvModexp.Proofs.Arm64.Exp.P2DRDefs
import FvModexp.Proofs.Arm64.Exp.CallWW

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `xOdd := nat(nil).rsh(x, i)` (nat.go:952; agent infra)

`rshCall`: from the `rsh` entry reached by `tzE` (memory `W1 (W0 …)`, `R0..R2 = 0`, `R3..R5 = x`, `R6 = tz`,
`R30 = rshR`) through asm's `Rsh.Hyp` (`CallWW.hypSum`; window `[sp - stkR, sp + aboveR)` inside ours) to `rshR`,
handing the callee's `RshPost` (with `z = nil`) to the continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

theorem w1_frame (M : Memory) {sp st lm zc zl yc yl yp zp lo : Nat} :
    MemFrame M (W1 M sp st lm zc zl yc yl yp zp lo) [(sp + 96, sp + 104), (sp + 120, sp + 208)] := by
  simp only [W1]
  refine MemFrame.writeLE ?_ _ (r := (sp + 96, sp + 104)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
  exact MemFrame.refl _ _

/-- the memory at the `rsh` call -/
@[reducible] def M1 (s : State) (zp zl zc st yp yl yc lm xp lo : Nat) : Memory :=
  W1 (W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) (s.sp.toNat - 112) st lm zc zl yc
    yl yp zp lo

theorem m1_frame (s : State) {stk A zp zl zc st yp yl yc lm xp lo : Nat} (hk : 120 ≤ stk) (hs : stk ≤ s.sp.toNat)
    (hA : 96 ≤ A) : MemFrame s.mem (M1 s zp zl zc st yp yl yc lm xp lo) (ownW s stk A) :=
  (w0_frame s.mem (by omega)).trans (w1_frame _) fun a k ho => by
    simp only [ownW, outside_cons, outside_nil, and_true] at ho ⊢; omega

theorem m1_regions (s : State) (zp zl zc st yp yl yc lm xp lo : Nat) :
    (M1 s zp zl zc st yp yl yc lm xp lo).regions = s.mem.regions := by
  simp only [M1, W1, W0, Memory.regions_writeLE]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the `rsh` call** -/
theorem rshCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains NHyp.fnP2 = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR + 112 ≤ stk) (haR : aboveR ≤ 88)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) {tz lo : Nat} (htz : tz < 2 ^ 64)
    (hbud : makeCost (Rsh.need xl tz) ≤ cst) {Q : State → Prop}
    (S : State) (hpc : S.pc = BitVec.ofNat 64 rshE) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 112))
    (r0 : S.regs 0 = 0#64) (r1 : S.regs 1 = 0#64) (r2 : S.regs 2 = 0#64) (r3 : S.regs 3 = BitVec.ofNat 64 xp)
    (r4 : S.regs 4 = BitVec.ofNat 64 xl) (r5 : S.regs 5 = BitVec.ofNat 64 xc) (r6 : S.regs 6 = BitVec.ofNat 64 tz)
    (r30 : S.regs 30 = BitVec.ofNat 64 rshR) (r28 : S.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat)
    (hm : S.mem = M1 s zp zl zc st yp yl yc lm xp lo)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 rshR → S'.sp = S.sp → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.regs 18 = S.regs 18 → S'.mem.regions = S.mem.regions →
      Rsh.RshPost R b L stkR aboveR 0 0 xp xl tz S S' → ReachesRet (LibW.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S Q := by
  have hC := hP.1
  have hC' := hC
  obtain ⟨⟨-, ⟨-, hle, -, -⟩, -, hwrt, -, -, hLs, -⟩, hsv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hcb, hinv⟩ := hC'
  have hX := hP.2.1
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by rw [hm]; exact m1_frame s (by omega) hle hA
  have hF0' : MemFrame s.mem S.mem (R.rt ++ ownW s stk A) := hF0.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hF0 hLs'
  have hrg : S.mem.regions = s.mem.regions := by rw [hm]; exact m1_regions s _ _ _ _ _ _ _ _ _ _
  have hwin : Outside (s.sp.toNat - stk) (stk + A) R.rt := hwrt
  have hinv1 : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) := by
    refine RtInv.inv_frame hF0 (fun r hr => ?_) hinv
    simp only [ownW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact hwin.of_sub (by omega) (by omega)
  have hSsp : S.sp.toNat + 112 = s.sp.toNat := by rw [hsp, BitVec.toNat_ofNat]; omega
  obtain ⟨hxR, hxn, hxN, -⟩ := in_sub hC (p := xp) (n := xl) (by simp) hF0' hLF0 (LiveExt.refl R L) hSsp
    (stk' := stkR) (A' := aboveR) (by omega) (by omega)
  have hS := CallWW.hypSum hap hns (hrh b L 0#64 0#64 0#64 (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
    (BitVec.ofNat 64 xc) (BitVec.ofNat 64 tz))
  have tx := tN (show xp < 2 ^ 64 by have := hxR.2.2.1; omega)
  have tl := tN (show xl < 2 ^ 64 by omega)
  have tc := tN (show xc < 2 ^ 64 by omega)
  have tt := tN htz
  simp only [BitVec.toNat_zero, tx, tl, tc, tt] at hS
  refine ReachesRet.call_regions hS (by rw [hpc]; rfl) ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_
  · rw [r30, tN (by simp only [rshR]; omega)]; exact ra_p2 hap hnf 107 (by decide)
  · simp only [ArgsFrom]; exact ⟨r0, r1, r2, r3, r4, r5, r6, trivial⟩
  · refine ⟨⟨CallW.callEnv_of (cenv_of hC hF0' hrg (LiveExt.refl R L) (by omega)) hsp r28 rfl (by omega) haR, hsv,
      Nat.le_refl _, ⟨by decide, by simp, fun h => absurd h (by omega)⟩, hxR, by omega, fun h => absurd h (by omega),
      hxN, hxl0, Or.inr rfl, by omega, by rw [r28, tN (BitVec.isLt _)]; exact hinv1⟩, hxc, hxc'⟩
  · exact K s' (hr.trans r30) e1 e2 e3 e4 hrg' hq

end

end FvModexp.Arm64.P2D
