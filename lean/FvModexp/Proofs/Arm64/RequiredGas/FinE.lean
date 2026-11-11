import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Seg

/-! `RequiredGas` (arm64) from `+0x260` to the return, case `¬ finK2 cap B` (combined in `Fin`). -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- From `+0x260` to the return, case `¬ finK2 cap B`. -/
theorem rg_fin2_E : Fin2If (fun len cap B E => ¬ finK2 cap B) := by
  intro c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM k2
  simp only [finK1, finK2, finK3] at k2
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd1 hd2 hdg
  have hrc : s.mem.readLE (c.toNat + 2) 1 = 1 := by rw [Memory.readLE_one]; exact ho2
  by_cases k1 : len.toNat - 96 < E.toNat + B.toNat <;> by_cases k3 : len.toNat - 96 < B.toNat + 32
  all_goals janus_run [hsp, h0, h1, h2, h18, h28, h29, m_ret, m_fp, m_c, m_ptr, m_len, m_cap, BitArith.and_asr63, BitArith.and_asr63_lit,
    Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt, k1, k2, k3, hrc] calls [sb, mv, og_summary]
  all_goals
    apply rgPost_of ptr len B E M s _ hB hE hM
    dsimp only
    rw [regs0_ret]
    refine congrArg (fun h => BitVec.ofNat 64 (Geth.osakaModexpGas B.toNat E.toNat M.toNat h)) ?_
    first
      | (unfold RgSpec.expHead L4; rw [if_neg (by omega)])
      | (rw [show s.sp.toNat - 312 = s.sp.toNat - 320 + 8 by omega, show s.sp.toNat - 304 = s.sp.toNat - 320 + 16 by omega,
            show s.sp.toNat - 296 = s.sp.toNat - 320 + 24 by omega]
         refine (L4_of (by assumption)).trans ?_
         unfold RgSpec.expHead
         rw [if_pos ⟨by omega, by omega⟩]
         refine fromBE_eq_of (by split <;> omega) (fun i hi => ?_)
         have hi2 : i < E.toNat ∧ i < 32 := by revert hi; split <;> intro hi <;> omega
         clear hi
         unfold Calldata.pad
         first
           | (rw [if_pos (by omega), show ptr.toNat + 96 + B.toNat + i = ptr.toNat + (96 + B.toNat + i) by omega]
              simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
              exact rd_frame hf (by simp only [outside_cons, outside_nil, and_true]; omega))
           | (by_cases hin : 96 + B.toNat + i < len.toNat
              · rw [if_pos hin]
                refine (copy_rd (by assumption) (by omega)).trans ?_
                rw [show ptr.toNat + 96 + B.toNat + i = ptr.toNat + (96 + B.toNat + i) by omega]
                simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
                exact rd_frame hf (by simp only [outside_cons, outside_nil, and_true]; omega)
              · rw [if_neg hin]
                refine (rd_out (by assumption) (by omega)).trans ?_
                rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with hq | hq | hq | hq <;>
                  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
                    Nat.zero_mod]))

end FvModexp.Arm64.RG
