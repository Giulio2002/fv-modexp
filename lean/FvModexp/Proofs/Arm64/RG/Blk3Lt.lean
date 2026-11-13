import Extracted
import FvModexp.Proofs.Arm64.RG.Seg

/-! `RequiredGas` (arm64) from `+0x160` (two length words parsed) to the return: the third `getData(input, 64, 32)` +
`SetBytes`, then `rg_fin1`. Case `len.toNat < cap.toNat` (combined in `Blk3`). -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_blk3_Lt (hsb : SbSum) (hmv : MvSum) (k : Fin1Stmt) : Blk3If (fun len cap => len.toNat < cap.toNat) := by
  intro c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_z0 w0 w1 d0
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c64 : len.toNat < 64 <;> by_cases c96 : len.toNat < 96 <;> by_cases d64 : 64 < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus_run [hsp, h0, h4, h18, h28, h29, m_ptr, m_len, m_cap, m_z0, c64, c96, d64, d0, BitArith.and_asr63,
    BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt] until [Extracted.entry + 0x204] calls [hsb, hmv]
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 64
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by with_reducible assumption) ?_
         refine fromBE_eq_of (by omega) (fun i hi => ?_)
         rg_byte)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0; rw [← w0]; unfold val256; janus_simp)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 32; rw [← w1]; unfold val256; janus_simp)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29]; decide)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29,
           Nat.reduceEqDiff, ite_true, ite_false, or_self, or_false, false_or, getD_cons_zero]
         first
           | done
           | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      | (with_reducible show Memory.readLE _ _ _ = _; janus_simp [m_ret, m_fp, m_c, m_ptr, m_len, m_cap, m_z0])

end FvModexp.Arm64.RG
