import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Seg

set_option autoImplicit false

/-! `RequiredGas` (amd64) from `+0x1d0` (two length words parsed) to the return: the third `getData(input, 64, 32)` +
`SetBytes`, then `rg_fin1`.  Case `len.toNat < cap.toNat` (combined in `Blk3`). -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_blk3_Lt (hsb : SbSum) (hmv : MvSum) (k : Fin1Stmt) : Blk3If (fun len cap => len.toNat < cap.toNat) := by
  intro c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_z0 w0 w1 d0
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  by_cases c64 : len.toNat < 64 <;> by_cases c96 : len.toNat < 96 <;> by_cases d64 : 64 < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus64_run [h4, h14, hx, h0, h2, m_ptr, m_len, m_cap, m_z0, c64, c96, d0, d64, neg_asr63_and', neg_asr63_and_lit', Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, BitVec.msb_eq_decide] until [Extracted.entry + 0x2c2] calls [hsb, hmv]
  all_goals try (exfalso; omega)
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    · with_reducible rfl
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero, h4, h14, h0, h2]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero, h4, h14, h0, h2]
    · dsimp only; simp only [ite_true, hx]; rfl
    · janus_frame
    · dl_close
    · janus64_simp [m_ret]
    · janus64_simp [m_fp]
    · janus64_simp [m_c]
    · janus64_simp [m_ptr]
    · janus64_simp [m_len]
    · janus64_simp [m_cap]
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero, h4, h14, h0, h2]
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero, h4, h14, h0, h2]
    · janus64_simp [m_z0]
    · janus64_simp [h0]
    · rw [← w0]; unfold val256; janus64_simp
    · rw [← w1]; unfold val256; janus64_simp
    · dsimp only
      refine Eq.trans (by with_reducible assumption) ?_
      refine fromBE_eq_of (by omega) (fun i hi => ?_)
      unfold Calldata.pad
      split
      all_goals rg_byte64

end FvModexp.Amd64.RG
