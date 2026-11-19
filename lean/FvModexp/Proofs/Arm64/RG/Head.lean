import Extracted
import FvModexp.Proofs.Arm64.RG.Seg

/-! `RequiredGas` (arm64) from the entry to `+0xc4` (the first `getData(input, 0, 32)` + `SetBytes`), then `Blk2Stmt` (a hypothesis,
as are the callee summaries: this module compiles in parallel with the other segments; `RequiredGas.lean` chains them). -/

set_option autoImplicit false

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_head (hsb : SbSum) (hmv : MvSum) (k : Blk2Stmt) (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') := by
  janus_ensures_old [FvModexp.Arm64.RG.RgPre, Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, FvModexp.Spec.OsakaReceiver]
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases d0 : len.toNat < cap.toNat
  all_goals janus_run [c32, d0, BitArith.and_asr63, BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0xc4] calls [hsb, hmv]
  all_goals
    refine reaches_of_returns (k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by with_reducible assumption) ?_
         refine fromBE_eq_of (by omega) (fun i hi => ?_)
         rg_byte)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply]; decide)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply,
           Nat.reduceEqDiff, ite_true, ite_false, or_self, or_false, false_or, getD_cons_zero]
         first
           | done
           | rfl
           | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      | (with_reducible show Memory.readLE _ _ _ = _; janus_simp; try (split <;> omega))

end FvModexp.Arm64.RG
