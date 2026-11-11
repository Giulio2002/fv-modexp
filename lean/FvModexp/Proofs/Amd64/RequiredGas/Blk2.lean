import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Seg

/-! `RequiredGas` (amd64) from `+0xf4` (the first length word parsed) to the return: the second `getData(input, 32, 32)` +
`SetBytes`, then `rg_blk3`. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_blk2 (k : Blk3Stmt) : Blk2Stmt := by
  intro c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_x5 w0 _
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases c64 : len.toNat < 64 <;> by_cases d0 : len.toNat < cap.toNat <;>
    by_cases d32 : 32 < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus64_run [h4, h14, hx, h0, h2, m_ptr, m_len, m_cap, m_x5, c32, c64, d0, d32, neg_asr63_and,
    neg_asr63_and_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, BitVec.msb_eq_decide] until [Extracted.entry + 0x1d0] calls [sb, mv]
  all_goals try (exfalso; omega)
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial)
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
    · janus64_simp [h0]
    · rw [← w0]; unfold val256; janus64_simp
    · dsimp only
      refine Eq.trans (by with_reducible assumption) ?_
      refine fromBE_eq_of (by omega) (fun i hi => ?_)
      unfold Calldata.pad
      split
      all_goals rg_byte64

end FvModexp.Amd64.RG
