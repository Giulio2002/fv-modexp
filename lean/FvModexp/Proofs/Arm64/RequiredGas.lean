import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk2

/-!
# `(*bigModExp).RequiredGas(input []byte) uint64` (arm64), go-ethereum v1.17.10 core/vm/contracts.go:606-646

**Guarantee** (`correctness`). For the Osaka receiver (`eip2565`, `eip7823`, `eip7883` all true) and every input slice, the call
returns (no fault, no panic) with the Go ABI preserved, and for every fork from Fusaka on, when the three length headers pass EIP-7823
(`Spec.LengthsPass`), the `uint64` result is EthLib's `requiredGas fork data (parseLengths data)` with `data` the input bytes.
-/

namespace FvModexp.Arm64.RequiredGas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp.Arm64.RG

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases d0 : len.toNat < cap.toNat
  all_goals janus_run [c32, d0, BitArith.and_asr63, BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0xc4] calls [sb, mv]
  all_goals
    refine reaches_of_returns (rg_blk2 c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by assumption) ?_
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

end FvModexp.Arm64.RequiredGas
