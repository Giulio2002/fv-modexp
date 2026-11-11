import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Fin1

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
  by_cases c32 : len.toNat < 32 <;> by_cases c64 : len.toNat < 64 <;> by_cases c96 : len.toNat < 96 <;>
    by_cases d0 : len.toNat < cap.toNat <;> by_cases d32 : 32 < cap.toNat <;> by_cases d64 : 64 < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus_run [c32, c64, c96, d0, d32, d64, BitArith.and_asr63, BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0x200] calls [sb, mv]
  all_goals trace_state
  all_goals sorry

end FvModexp.Arm64.RequiredGas
