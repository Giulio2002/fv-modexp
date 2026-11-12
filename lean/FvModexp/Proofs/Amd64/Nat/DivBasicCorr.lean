import FvModexp.Proofs.Amd64.Nat.DivBasicDefs
import FvModexp.Proofs.Common.DivBasicMach

set_option autoImplicit false

/-!
# `divBasic` (amd64): the `for greaterThan(x1, x2, rhat, ujn2)` correction loop (natdiv.go:684-696)

Code (`ctest = fn + 0x57e`, body `fn + 0x574`, exit `fn + 0x59e`):
```
+0x574 MOVQ DX, BX; MOVQ AX, R9; MULQ SI; NOP; NOPW         -- rhat = rhat'; qhat = qhat'; DX:AX = qhat·vn2
+0x57e (NOPW) CMPQ BX, DX; JB dec; JNE out; CMPQ AX, R8; JBE out   -- greaterThan(x1 = DX, x2 = AX, rhat = BX, ujn2 = R8)
  dec: LEAQ (BX)(R13*1), DX; LEAQ -1(R9), AX; CMPQ BX, DX; JBE +0x574; JMP exit   -- qhat--; rhat += vn1; overflow
  out: MOVQ R9, AX
+0x59e exit (RAX = qhat)
```
Registers: `R9 = qhat`, `RBX = rhat`, `RDX = x1`, `RAX = x2`, `RSI = vn2`, `R8 = ujn2`, `R13 = vn1`. The twin of
`Arm64/Nat/DivBasicCorr.lean` (same model `Mdl.corrLoop`, same fuel induction).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

abbrev ctest : Nat := segAddr Extracted.program fn + 0x57e
abbrev cexit : Nat := segAddr Extracted.program fn + 0x59e

theorem bv_dec (q : Nat) (hq : q < 2 ^ 64) :
    BitVec.ofNat 64 q - 1#64 = BitVec.ofNat 64 ((q + 2 ^ 64 - 1) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bv_add' (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 ((a + b) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem cl_go (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : Mdl.greaterThan x1 x2 rhat un2)
    (hno : rhat ≤ (rhat + vn1) % 2 ^ 64) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 =
      Mdl.corrLoop vn1 vn2 un2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((rhat + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) := by
  rw [Mdl.corrLoop, if_pos hg, if_neg (by omega)]
  rfl

theorem cl_ovf (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : Mdl.greaterThan x1 x2 rhat un2)
    (hov : ¬ rhat ≤ (rhat + vn1) % 2 ^ 64) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 = (qhat + 2 ^ 64 - 1) % 2 ^ 64 := by
  rw [Mdl.corrLoop, if_pos hg, if_pos (by omega)]

theorem cl_stop (vn1 vn2 un2 F qhat rhat x1 x2 : Nat) (hg : ¬ Mdl.greaterThan x1 x2 rhat un2) :
    Mdl.corrLoop vn1 vn2 un2 (F + 1) qhat rhat x1 x2 = qhat := by
  rw [Mdl.corrLoop, if_neg hg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
theorem corr (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (vn1 vn2 un2 : Nat)
    (hv1 : 0 < vn1) (hv1B : vn1 < 2 ^ 64) (hv2 : vn2 < 2 ^ 64) (hu2 : un2 < 2 ^ 64) :
    ∀ (F qhat rhat x1 x2 : Nat) (S : State), S.rip = BitVec.ofNat 64 ctest →
      S.regs 9 = BitVec.ofNat 64 qhat → S.regs 3 = BitVec.ofNat 64 rhat → S.regs 2 = BitVec.ofNat 64 x1 →
      S.regs 0 = BitVec.ofNat 64 x2 → S.regs 6 = BitVec.ofNat 64 vn2 → S.regs 8 = BitVec.ofNat 64 un2 →
      S.regs 13 = BitVec.ofNat 64 vn1 → qhat < 2 ^ 64 → rhat < 2 ^ 64 → x1 < 2 ^ 64 → x2 < 2 ^ 64 →
      2 ^ 64 ≤ F + rhat →
      (∀ S' : State, S'.rip = BitVec.ofNat 64 cexit →
        S'.regs 0 = BitVec.ofNat 64 (Mdl.corrLoop vn1 vn2 un2 F qhat rhat x1 x2) →
        (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 9 → S'.regs i = S.regs i) → S'.mem = S.mem → S'.xmm = S.xmm →
        S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) →
      ReachesRet (LibDivBasic.program.link impl) r S Q
  | 0, qhat, rhat, x1, x2, S, _, _, _, _, _, _, _, _, _, hr, _, _, hF, _ => by omega
  | F + 1, qhat, rhat, x1, x2, S, hpc, h9, h3, h2, h0, h6, h8, h13, hq, hr, hx1, hx2, hF, hk => by
    have hq' : qhat % 2 ^ 64 = qhat := Nat.mod_eq_of_lt hq
    have hr' : rhat % 2 ^ 64 = rhat := Nat.mod_eq_of_lt hr
    have hx1' : x1 % 2 ^ 64 = x1 := Nat.mod_eq_of_lt hx1
    have hx2' : x2 % 2 ^ 64 = x2 := Nat.mod_eq_of_lt hx2
    have hv1' : vn1 % 2 ^ 64 = vn1 := Nat.mod_eq_of_lt hv1B
    have hv2' : vn2 % 2 ^ 64 = vn2 := Nat.mod_eq_of_lt hv2
    have hu2' : un2 % 2 ^ 64 = un2 := Nat.mod_eq_of_lt hu2
    have eq1 : (18446744073709551615 + qhat) % 18446744073709551616 = (qhat + 2 ^ 64 - 1) % 2 ^ 64 := by omega
    have hq1 : (qhat + 2 ^ 64 - 1) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
    have hx1n : (qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64 < 2 ^ 64 :=
      Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hq1 (by omega) (by omega))
    have hx2n : (qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
    have bx2 : BitVec.ofNat 64 ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2) =
        BitVec.ofNat 64 ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]
    janus64_run [h9, h3, h2, h0, h6, h8, h13, hq', hr', hx1', hx2', hv1', hv2', hu2'] until [ctest, cexit]
    · -- `x1 > rhat`, no overflow: next round
      rename_i hgt
      have hno := hbr
      have hno' : rhat ≤ (rhat + vn1) % 2 ^ 64 := by omega
      have hF' : 2 ^ 64 ≤ F + (rhat + vn1) % 2 ^ 64 := by omega
      rw [eq1]
      refine corr impl r Q vn1 vn2 un2 hv1 hv1B hv2 hu2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((rhat + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) _ ?gpc
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq1 (Nat.mod_lt _ (by omega)) hx1n hx2n hF' ?gk
      case gpc => janus64_simp
      case gk =>
        intro S' hp e0 hregs em ex efs edf
        refine hk S' hp ?_ (fun i a b c d => by rw [hregs i a b c d]; simp only [setRegF_apply, a, b, c, d, if_false])
          em ex efs edf
        rw [e0, cl_go vn1 vn2 un2 F qhat rhat x1 x2 (Or.inl hgt) hno']
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq, bv_add', h6, h8, h13, bx2]
    · -- `x1 > rhat`, overflow: break
      rename_i hgt
      have hov := hbr
      have hov' : ¬ rhat ≤ (rhat + vn1) % 2 ^ 64 := by omega
      refine hk _ ?gpc ?_ (fun i a b c d => by simp only [setRegF_apply, a, b, c, d, if_false]) rfl rfl rfl rfl
      case gpc => janus64_simp
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq]
      rw [cl_ovf vn1 vn2 un2 F qhat rhat x1 x2 (Or.inl hgt) hov']
    · -- `x1 = rhat`, `x2 ≤ ujn2`: stop
      rename_i hlt heq
      have hle := hbr
      refine hk _ ?gpc ?_ (fun i a b c d => by simp only [setRegF_apply, a, b, c, d, if_false]) rfl rfl rfl rfl
      case gpc => janus64_simp
      simp only [setRegF_apply, ↓reduceIte]
      rw [cl_stop vn1 vn2 un2 F qhat rhat x1 x2 (by unfold Mdl.greaterThan; omega)]
    · -- `x1 = rhat`, `x2 > ujn2`, no overflow: next round
      rename_i hlt heq hgt
      have hno := hbr
      have hx : x1 = rhat := by omega
      subst hx
      have hno' : x1 ≤ (x1 + vn1) % 2 ^ 64 := by omega
      have hF' : 2 ^ 64 ≤ F + (x1 + vn1) % 2 ^ 64 := by omega
      rw [eq1]
      refine corr impl r Q vn1 vn2 un2 hv1 hv1B hv2 hu2 F ((qhat + 2 ^ 64 - 1) % 2 ^ 64) ((x1 + vn1) % 2 ^ 64)
        ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 / 2 ^ 64) ((qhat + 2 ^ 64 - 1) % 2 ^ 64 * vn2 % 2 ^ 64) _ ?gpc
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq1 (Nat.mod_lt _ (by omega)) hx1n hx2n hF' ?gk
      case gpc => janus64_simp
      case gk =>
        intro S' hp e0 hregs em ex efs edf
        refine hk S' hp ?_ (fun i a b c d => by rw [hregs i a b c d]; simp only [setRegF_apply, a, b, c, d, if_false])
          em ex efs edf
        rw [e0, cl_go vn1 vn2 un2 F qhat x1 x1 x2 (Or.inr ⟨rfl, by omega⟩) hno']
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq, bv_add', h6, h8, h13, bx2]
    · -- `x1 = rhat`, `x2 > ujn2`, overflow: break
      rename_i hlt heq hgt
      have hov := hbr
      have hx : x1 = rhat := by omega
      subst hx
      have hov' : ¬ x1 ≤ (x1 + vn1) % 2 ^ 64 := by omega
      refine hk _ ?gpc ?_ (fun i a b c d => by simp only [setRegF_apply, a, b, c, d, if_false]) rfl rfl rfl rfl
      case gpc => janus64_simp
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, bv_dec qhat hq]
      rw [cl_ovf vn1 vn2 un2 F qhat x1 x1 x2 (Or.inr ⟨rfl, by omega⟩) hov']
    · -- `x1 < rhat`: stop
      rename_i hlt
      have hne := hbr
      refine hk _ ?gpc ?_ (fun i a b c d => by simp only [setRegF_apply, a, b, c, d, if_false]) rfl rfl rfl rfl
      case gpc => janus64_simp
      simp only [setRegF_apply, ↓reduceIte]
      rw [cl_stop vn1 vn2 un2 F qhat rhat x1 x2 (by unfold Mdl.greaterThan; omega)]

end FvModexp.Amd64.DivBasic
