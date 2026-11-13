import Extracted
import FvModexp.Proofs.Arm64.RG.Seg

/-! `RequiredGas` (arm64) from `+0xc4` (the first length word parsed) to the return: the second `getData(input, 32, 32)` +
`SetBytes`, then `rg_blk3`. Case `len.toNat < cap.toNat` (combined in `Blk2`). -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_blk2_Lt (hsb : SbSum) (hmv : MvSum) (k : Blk3Stmt) : Blk2If (fun len cap => len.toNat < cap.toNat) := by
  intro c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_x5 w0 d0
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases c64 : len.toNat < 64 <;> by_cases d32 : 32 < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus_run [hsp, h0, h4, h18, h28, h29, m_ptr, m_len, m_cap, m_x5, c32, c64, d32, d0, BitArith.and_asr63,
    BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt] until [Extracted.entry + 0x160] calls [hsb, hmv]
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 32
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by with_reducible assumption) ?_
         refine fromBE_eq_of (by omega) (fun i hi => ?_)
         rg_byte)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0; rw [← w0]; unfold val256; janus_simp)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29]; decide)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29,
           Nat.reduceEqDiff, ite_true, ite_false, or_self, or_false, false_or, getD_cons_zero]
         first
           | done
           | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      | (with_reducible show Memory.readLE _ _ _ = _; janus_simp [m_ret, m_fp, m_c, m_ptr, m_len, m_cap])

end FvModexp.Arm64.RG
