import FvModexp.Proofs.Arm64.Nat.DivBasicDefs
import FvModexp.Proofs.Common.DivBasicMach

/-!
# `divBasic` (arm64): the `for greaterThan(x1, x2, rhat, ujn2)` correction loop (natdiv.go:684-696)

Code (`ctest = fn + 0x380`, body `fn + 0x36c`, exit `fn + 0x3a4`):
```
+0x36c NOOP; MUL R0,R3,R11; UMULH R0,R3,R7; MOVD R6,R1; MOVD R11,R6     -- x1, x2 = mulWW(qhat, vn2); rhat = rhat'
+0x380 CMP R7,R1; BCC body'; BNE exit; CMP R5,R6; BLS exit               -- greaterThan(x1, x2, rhat, ujn2)
       body': ADD R1,R10,R6; SUB $1,R0,R0; CMP R6,R1; BLS +0x36c           -- qhat--; rhat' = rhat + vn1; no overflow
+0x3a4 exit
```
Registers: `R0 = qhat`, `R1 = rhat`, `R7 = x1`, `R6 = x2`, `R3 = vn2`, `R5 = ujn2`, `R10 = vn1`. `corr` (induction on the
fuel `F ≥ 2^64 - rhat`, `rhat` strictly increases): the loop exits with `R0 = Mdl.corrLoop … F qhat rhat x1 x2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivBasic

abbrev ctest : Nat := segAddr Extracted.program fn + 0x380
abbrev cexit : Nat := segAddr Extracted.program fn + 0x3a4

theorem bv_dec (q : Nat) (hq : q < 2 ^ 64) :
    BitVec.ofNat 64 q - 1#64 = BitVec.ofNat 64 ((q + 2 ^ 64 - 1) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bv_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 ((b + a) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bv_mul (a q : Nat) (hq : q < 2 ^ 64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 q = BitVec.ofNat 64 (q * (a % 2 ^ 64) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hq]
  rw [Nat.mul_comm]

theorem bv_umulh (a q : Nat) (ha : a < 2 ^ 64) (hq : q < 2 ^ 64) :
    BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 a) * BitVec.setWidth 128 (BitVec.ofNat 64 q)) =
      BitVec.ofNat 64 (q * a / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [Janus.Tactic.umulh_toNat]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hq]
  have : q * a / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by omega)
  rw [Nat.mod_eq_of_lt this, Nat.mul_comm]

theorem cl_go (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : Mdl.greaterThan x1 x2 rhat un2)
    (hno : rhat ≤ (vn1 + rhat) % 2 ^ 64) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 =
      Mdl.corrLoop vn1 vn2 un2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((rhat + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) := by
  have e : (rhat + vn1) % 2 ^ 64 = (vn1 + rhat) % 2 ^ 64 := by rw [Nat.add_comm]
  rw [Mdl.corrLoop, if_pos hg, if_neg (by rw [e]; omega)]
  rfl

theorem cl_ovf (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : Mdl.greaterThan x1 x2 rhat un2)
    (hov : ¬ rhat ≤ (vn1 + rhat) % 2 ^ 64) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 = (qhat + 2 ^ 64 - 1) % 2 ^ 64 := by
  have e : (rhat + vn1) % 2 ^ 64 = (vn1 + rhat) % 2 ^ 64 := by rw [Nat.add_comm]
  rw [Mdl.corrLoop, if_pos hg, if_pos (by rw [e]; omega)]

theorem cl_stop (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : ¬ Mdl.greaterThan x1 x2 rhat un2) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 = qhat := by
  rw [Mdl.corrLoop, if_neg hg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 400000 in
theorem corr (impl : List Segment) (r : BitVec 64) (Q : State → Prop) (vn1 vn2 un2 : Nat)
    (hv1 : 0 < vn1) (hv1B : vn1 < 2 ^ 64) (hv2 : vn2 < 2 ^ 64) (hu2 : un2 < 2 ^ 64) :
    ∀ (F qhat rhat x1 x2 : Nat) (S : State), S.pc = BitVec.ofNat 64 ctest →
      S.regs 0 = BitVec.ofNat 64 qhat → S.regs 1 = BitVec.ofNat 64 rhat → S.regs 7 = BitVec.ofNat 64 x1 →
      S.regs 6 = BitVec.ofNat 64 x2 → S.regs 3 = BitVec.ofNat 64 vn2 → S.regs 5 = BitVec.ofNat 64 un2 →
      S.regs 10 = BitVec.ofNat 64 vn1 → qhat < 2 ^ 64 → rhat < 2 ^ 64 → x1 < 2 ^ 64 → x2 < 2 ^ 64 →
      2 ^ 64 ≤ F + rhat →
      (∀ S' : State, S'.pc = BitVec.ofNat 64 cexit →
        S'.regs 0 = BitVec.ofNat 64 (Mdl.corrLoop vn1 vn2 un2 F qhat rhat x1 x2) →
        S'.regs 10 = BitVec.ofNat 64 vn1 → S'.mem = S.mem → S'.sp = S.sp → S'.regs 28 = S.regs 28 →
        S'.regs 29 = S.regs 29 → S'.regs 18 = S.regs 18 → ReachesRet (LibDivBasic.program.link impl) r S' Q) →
      ReachesRet (LibDivBasic.program.link impl) r S Q
  | 0, qhat, rhat, x1, x2, S, _, _, _, _, _, _, _, _, _, hr, _, _, hF, _ => by omega
  | F + 1, qhat, rhat, x1, x2, S, hpc, h0, h1, h7, h6, h3, h5, h10, hq, hr, hx1, hx2, hF, hk => by
    have hq' : qhat % 2 ^ 64 = qhat := Nat.mod_eq_of_lt hq
    have hr' : rhat % 2 ^ 64 = rhat := Nat.mod_eq_of_lt hr
    have hx1' : x1 % 2 ^ 64 = x1 := Nat.mod_eq_of_lt hx1
    have hx2' : x2 % 2 ^ 64 = x2 := Nat.mod_eq_of_lt hx2
    have hv1' : vn1 % 2 ^ 64 = vn1 := Nat.mod_eq_of_lt hv1B
    have hv2' : vn2 % 2 ^ 64 = vn2 := Nat.mod_eq_of_lt hv2
    have hu2' : un2 % 2 ^ 64 = un2 := Nat.mod_eq_of_lt hu2
    janus_run [h0, h1, h7, h6, h3, h5, h10, hq', hr', hx1', hx2', hv1', hv2', hu2'] until [ctest, cexit]
    · -- `x1 > rhat`, no overflow: next round
      rename_i hgt
      have hq1 : (qhat + 2 ^ 64 - 1) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
      have hF' : 2 ^ 64 ≤ F + (rhat + vn1) % 2 ^ 64 := by omega
      refine corr impl r Q vn1 vn2 un2 hv1 hv1B hv2 hu2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((rhat + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) _ ?gpc
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq1
        (Nat.mod_lt _ (by omega)) (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hq1 (by omega) (by omega)))
        (Nat.mod_lt _ (by omega)) hF' ?gk
      case gpc => janus_simp
      case gk =>
        intro S' hp e0 e10 em es e28 e29 e18
        refine hk S' hp ?_ e10 em es e28 e29 e18
        rw [e0, cl_go vn1 vn2 un2 F qhat rhat x1 x2 (Or.inl hgt) hbr]
      all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq, bv_add,
        bv_mul _ _ hq1, bv_umulh _ _ hv2 hq1, Nat.mod_eq_of_lt hv2, h3, h5, h10]
    · -- `x1 > rhat`, overflow: break
      rename_i hgt
      refine hk _ ?gpc ?_ ?_ rfl rfl rfl rfl rfl
      case gpc => janus_simp
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq]
        rw [cl_ovf vn1 vn2 un2 F qhat rhat x1 x2 (Or.inl hgt) hbr]
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10]
    · -- `x1 = rhat`, `x2 ≤ ujn2`: stop
      rename_i hlt heq
      refine hk _ ?gpc ?_ h10 rfl rfl rfl rfl rfl
      case gpc => janus_simp
      rw [h0, cl_stop vn1 vn2 un2 F qhat rhat x1 x2 (by unfold Mdl.greaterThan; omega)]
    · -- `x1 = rhat`, `x2 > ujn2`, no overflow: next round
      rename_i hlt heq hgt
      subst heq
      have hq1 : (qhat + 2 ^ 64 - 1) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
      have hF' : 2 ^ 64 ≤ F + (rhat + vn1) % 2 ^ 64 := by omega
      refine corr impl r Q vn1 vn2 un2 hv1 hv1B hv2 hu2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((rhat + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) _ ?gpc
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq1
        (Nat.mod_lt _ (by omega)) (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hq1 (by omega) (by omega)))
        (Nat.mod_lt _ (by omega)) hF' ?gk
      case gpc => janus_simp
      case gk =>
        intro S' hp e0 e10 em es e28 e29 e18
        refine hk S' hp ?_ e10 em es e28 e29 e18
        rw [e0, cl_go vn1 vn2 un2 F qhat rhat rhat x2 (Or.inr ⟨rfl, by omega⟩) hbr]
      all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq, bv_add,
        bv_mul _ _ hq1, bv_umulh _ _ hv2 hq1, Nat.mod_eq_of_lt hv2, h3, h5, h10]
    · -- `x1 = rhat`, `x2 > ujn2`, overflow: break
      rename_i hlt heq hgt
      subst heq
      refine hk _ ?gpc ?_ ?_ rfl rfl rfl rfl rfl
      case gpc => janus_simp
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq]
        rw [cl_ovf vn1 vn2 un2 F qhat rhat rhat x2 (Or.inr ⟨rfl, by omega⟩) hbr]
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10]
    · -- `x1 < rhat`: stop
      rename_i hlt
      refine hk _ ?gpc ?_ h10 rfl rfl rfl rfl rfl
      case gpc => janus_simp
      rw [h0, cl_stop vn1 vn2 un2 F qhat rhat x1 x2 (by unfold Mdl.greaterThan; omega)]

end FvModexp.Arm64.DivBasic
