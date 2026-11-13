import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Seg

/-! `RequiredGas` (amd64) from `+0x324` to the return, case `¬ finS len B ∧ finE E ∧ finN1 len B` (combined in `Fin`). -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- From `+0x324` to the return, case `¬ finS len B ∧ finE E ∧ finN1 len B`. -/
theorem rg_fin2_A (hsb : SbSum) (hmv : MvSum) (hog : OgSum) : Fin2If (fun len B E => ¬ finS len B ∧ finE E ∧ finN1 len B) := by
  intro c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM ⟨kS, kE, kN⟩
  simp only [finS, finE, finN1] at kS kE kN
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  have hrc : s.mem.readLE (c.toNat + 2) 1 = 1 := by rw [Janus.Arm64.Memory.readLE_one]; exact ho2
  have c96 : ¬ len.toNat ≤ 96 := by omega
  have kB : B.toNat < cap.toNat - 96 := by omega
  have hc96 : (cap - 96#64).toNat = cap.toNat - 96 := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  all_goals janus64_run [h4, h14, hx, h0, h1, h3, m_ret, m_fp, m_c, m_ptr, m_len, m_cap, kS, kE, kN, kB, c96, hc96, hrc, neg_asr63_and', neg_asr63_and_lit', neg_asr63_and, neg_asr63_and_lit,
    Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, BitVec.msb_eq_decide]
    calls [hsb, hmv, hog]
  all_goals
    apply rgPost_of ptr len B E M s _ hB hE hM
    dsimp only
    simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, getD_cons_zero]
    refine congrArg (fun h => BitVec.ofNat 64 (Geth.osakaModexpGas B.toNat E.toNat M.toNat h)) ?_
    unfold RgSpec.expHead; rw [if_pos ⟨by omega, by omega⟩]
    unfold ogHead
    janus64_simp [rd16_lo, rd16_hi]
    rw [show (s.regs 4).toNat - 304 = (s.regs 4).toNat - 320 + 16 by omega, Nat.add_assoc, L4_val256]
    refine Eq.trans (by with_reducible assumption) ?_
    refine fromBE_eq_of (by split <;> omega) (fun i hi => ?_)
    have hi2 : i < 32 := by revert hi; split <;> intro hi <;> omega
    clear hi
    unfold Calldata.pad
    split
    all_goals rg_byte64

end FvModexp.Amd64.RG
