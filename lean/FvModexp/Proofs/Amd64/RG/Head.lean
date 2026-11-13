import Extracted
import FvModexp.Proofs.Amd64.RG.Seg

/-! `RequiredGas` (amd64) from the entry to `+0xf4` (the first `getData(input, 0, 32)` + `SetBytes`), then `Blk2Stmt` (a hypothesis,
as are the callee summaries: this module compiles in parallel with the other segments; `RequiredGas.lean` chains them). -/

set_option autoImplicit false

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_head (hsb : SbSum) (hmv : MvSum) (k : Blk2Stmt) (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  janus64_data hd [hacc]
  by_cases c32 : len.toNat < 32
  all_goals janus64_run [c32, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0xf4] calls [hsb, hmv]
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial)
      (fun s' h => h)
    · with_reducible rfl
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · dsimp only; simp only [ite_true]; rfl
    · janus_frame
    · dl_close
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · janus64_simp; split <;> omega
    · dsimp only
      refine Eq.trans (by with_reducible assumption) ?_
      refine fromBE_eq_of (by omega) (fun i hi => ?_)
      set_option maxHeartbeats 2000000 in
      unfold Calldata.pad
      split
      · first
          | (refine (copy_rd (by with_reducible assumption) (by omega)).trans ?_
             simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
             exact rd_self (by omega))
          | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
             exact rd_self (by omega))
      · first
          | (exfalso; omega)
          | (refine (rd_out (by with_reducible assumption) (by omega)).trans ?_
             rcases (show i < 16 ∨ (16 ≤ i ∧ i < 32) by omega) with hq | hq <;>
               simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
                 Nat.zero_div, Nat.zero_mod])


end FvModexp.Amd64.RG
