import FvModexp.Proofs.Amd64.Exp.P2DWin

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the odd-base summary `sumO` (agent asm s68; amd64 twin of infra's arm64 `P2DSumO`)

`sumO`: a `Summary` on `LibW` at `fnE` for an ODD base `X` (no recursion): `entP`, then `logM = 1` → `oneP`;
otherwise `winR` → `winCall` with the window summaries `hW2 : WSum … w2E kW2 c2`, `hW4 : WSum … w4E kW4 c4`
(premises: divmc's `P2W2` via `wsum2`, top's `P2W4`). Generic in the window top `A` (`72 ≤ A`).
Budget `costO c2 c4 (stLen …) yl lm`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- the extra entry facts of the odd path (`X15`, DF, `zp`, `x` odd, `cap x`, `NHyp.XGc`'s first three, RA bound) -/
@[reducible] def OX (s : State) (zp xp xl xc : Nat) : Prop :=
  (s.xmm 15 = 0 ∧ s.df = false ∧ zp < 2 ^ 64) ∧ natVal s.mem xp xl % 2 = 1 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
    ((0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 ∧
      s.mem.accessible Callees.adxAddr 1 false = true) ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

theorem bv_tn (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`expNNPowerOfTwo` on an odd base** (Summary on `LibW`) -/
theorem sumO {impl : List Amd64.Segment} {R : RtInv}
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    {kW2 kW4 : Nat} {c2 c4 : Nat → Nat → Nat → Nat} (hW2 : WSum impl R w2E kW2 c2) (hW4 : WSum impl R w4E kW4 c4)
    (b : Nat) (L : List (Nat × Nat)) (stk A : Nat) (hk1 : 4320 ≤ stk) (hkW2 : kW2 + 0x78 ≤ stk)
    (hkW4 : kW4 + 0x78 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x78) (hA : 72 ≤ A)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) :
    Summary (LibW.program.link impl) fnE
      (fun s => Regs s zp zl zc st xp xl xc yp yl yc lm ∧
        PreD R b L stk A (costO c2 c4 (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧ OX s zp xp xl xc)
      (fun s s' => PostD R b L stk A (costO c2 c4 (stLen s.mem st) yl lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s') := by
  intro s hpc ⟨hR, hP, ⟨hx15, hdf, hzp⟩, hXo, hxl, hxc, hEX, hra⟩
  have hP' := hP
  obtain ⟨hC, hX, hY, hlm1, hlm, -, -⟩ := hP'
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hx0 : s.mem.readLE xp 8 % 2 = 1 := by
    have := val_mod2 s.mem xp xl 1 hxl0 (by omega); rw [Nat.pow_one] at this; omega
  have hy := hR.2.2.2.2.2.2.2.2
  refine entP _ s hP hk1 hA hpc hR (fun hl S hS hRE hm => ?_) (fun hl _ S hS hRE hm => ?_)
    (fun _ h _ => absurd h (by omega)) (fun _ h _ => absurd h (by omega))
  · exact oneP hmk hP hk1 hA (Nat.le_add_left _ _) hl hra S hS hRE hm
  · obtain ⟨⟨-, ⟨hbel, h48, hacc⟩, -, -, -, -, -, -, -⟩, -, -, -, -, -, -, hins, -⟩ := hC
    simp only [regSP] at hbel h48 hacc
    obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, hyN, -⟩ := hins yp yl (by simp)
    have hyl0 : 0 < yl := by
      rcases Nat.eq_zero_or_pos yl with h | h
      · subst h; simp [natVal] at hY
      · exact h
    obtain ⟨esp, -, e0, e3, e1, e7, e6, e8, e9, e10, e11, e2, e14, efs, ex, edf⟩ := hRE
    simp only [win, outside_cons, outside_nil, and_true] at hyw
    have hyaW : S.mem.accessible (yp + 8 * (yl - 1)) 8 false = true := by
      rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega))
    have hyt : S.mem.readLE (yp + 8 * (yl - 1)) 8 = s.mem.readLE (yp + 8 * (yl - 1)) 8 := by
      rw [hm]; exact w0_rd (by omega)
    have hw0 : S.mem.readLE (yp + 8 * (yl - 1)) 8 ≠ 0 := by
      rw [hyt]; rcases hyN with h | h
      · omega
      · exact h
    have haccS : S.mem.accessible ((s.regs 4).toNat - 0x70 - 8) 0x20 true = true := by
      rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    have haccS2 : S.mem.accessible ((s.regs 4).toNat - 0x70 + 0x88) 8 false = true := by
      rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    have e14' : S.regs 14 = s.regs 14 := by rw [e14]; exact bv_tn _
    refine winR _ _ ((s.regs 4).toNat - 0x70) yp yl lm _ S.mem (by omega) (by omega) hlm hy48 hyaW rfl hw0
      (by omega) (by omega) haccS haccS2 S hS esp e11 e2 e10 rfl
      fun c hc S1 h1pc h1sp a0 a3 a1 a7 a6 a8 a9 a10 a5 a14 afs ax adf h1m => ?_
    have esp1 : S1.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x78) := by
      rw [h1sp, show (s.regs 4).toNat - 0x70 - 8 = (s.regs 4).toNat - 0x78 by omega]
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact winCall (r := w2R) hP hk1 hA hXo (by omega)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)) hra hxl hxc hEX hzp hx15 hdf hy hW2 (by omega) hk2
        (by simp) S1 h1pc esp1 (a0.trans e0) (a3.trans e3) (a1.trans e1) (a7.trans e7) (a6.trans e6) (a8.trans e8)
        (a9.trans e9) (a10.trans e10) (a14.trans e14') (afs.trans efs) (ax.trans ex) (adf.trans edf)
        (by rw [h1m, hm]; rfl)
    · exact winCall (r := w4R) hP hk1 hA hXo (by omega)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)) hra hxl hxc hEX hzp hx15 hdf hy hW4 (by omega) hk2
        (by simp) S1 h1pc esp1 (a0.trans e0) (a3.trans e3) (a1.trans e1) (a7.trans e7) (a6.trans e6) (a8.trans e8)
        (a9.trans e9) (a10.trans e10) (a14.trans e14') (afs.trans efs) (ax.trans ex) (adf.trans edf)
        (by rw [h1m, hm]; rfl)

end FvModexp.Amd64.P2D
