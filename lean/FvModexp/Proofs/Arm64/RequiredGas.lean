import Extracted
import FvModexp.Spec
import FvModexp.Proofs.Common.Calldata
import FvModexp.Proofs.Common.BitArith
import FvModexp.Proofs.Arm64.RequiredGas.Mv
import FvModexp.Proofs.Arm64.RequiredGas.Sb
import FvModexp.Proofs.Arm64.RequiredGas.Og

namespace FvModexp.Arm64.RequiredGas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp.Arm64.RG

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem explore (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544)
      (fun s s' => True) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases c64 : len.toNat < 64 <;> by_cases c96 : len.toNat < 96
  all_goals try (exfalso; omega)
  all_goals janus_run [c32, c64, c96, BitArith.and_asr63, BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt] until [Extracted.entry + 0xc0] calls [sb, mv, og_summary]
  all_goals trace_state
  all_goals sorry

end FvModexp.Arm64.RequiredGas
