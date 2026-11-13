import Extracted
import FvModexp.Proofs.Amd64.RG.Blk2
import FvModexp.Proofs.Amd64.RG.Blk3
import FvModexp.Proofs.Amd64.RG.Fin1
import FvModexp.Proofs.Amd64.RG.Fin
import FvModexp.Proofs.Amd64.RG.Head
import FvModexp.Proofs.Amd64.RG.Wit
import FvModexp.Proofs.Amd64.RG.Sb
import FvModexp.Proofs.Amd64.RG.Mv
import FvModexp.Proofs.Amd64.RG.Og

/-!
# `(*bigModExp).RequiredGas(input []byte) uint64` (amd64), go-ethereum v1.17.10 core/vm/contracts.go:606-646

**Guarantee** (`correctness`). For the Osaka receiver (`eip2565`, `eip7823`, `eip7883` all true, `RAX`) and every input slice
(`RBX`, `RCX`, `RDI`), the call returns (no fault, no panic) with the Go ABI preserved, and for every fork from Fusaka on, when the
three length headers pass EIP-7823 (`Spec.LengthsPass`), the `uint64` result (`RAX`) is EthLib's `requiredGas fork data
(parseLengths data)` with `data` the input bytes.
-/

namespace FvModexp.Amd64.RequiredGas

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp.Amd64.RG

theorem run (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') :=
  rg_head sb mv (rg_blk2 sb mv (rg_blk3 sb mv (rg_fin1 (rg_fin2 sb mv og_summary)))) c ptr len cap

/-- **Row 2 (amd64).** `(*bigModExp).RequiredGas` with the Osaka receiver: returns for every input, and when the lengths pass EIP-7823
the result is EthLib's `requiredGas` at every fork from Fusaka on. -/
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ Buffer s ptr len.toNat false ∧ Buffer s c 3 false ∧
        Spec.OsakaReceiver s.mem c.toNat ∧ Janus.Spec.Disjoint ptr.toNat len.toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint c.toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536)
      (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) := by
  intro ret hret s hs ⟨h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have h2 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := by
    have hr := hs.ret; simp only [regSP, Janus.Amd64.Program.withExit] at hr; rw [hr]; exact hret.user
  exact run c ptr len cap ret hret s hs ⟨⟨h1, h2, h3⟩, h4, h5, hs.zero, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

namespace Witness

/-- **Non-vacuity**: a concrete Osaka-receiver call with 96 zero bytes satisfies the precondition (and returns). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, ptr, len, cap] s ∧
    (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ Buffer s ptr len.toNat false ∧ Buffer s c 3 false ∧
        Spec.OsakaReceiver s.mem c.toNat ∧ Janus.Spec.Disjoint ptr.toNat len.toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint c.toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) s s' :=
  ⟨RG.Wit.ret, RG.Wit.s0, _, _, _, _, RG.Wit.hret, RG.Wit.setup, RG.Wit.hpre,
    correctness _ _ _ _ RG.Wit.ret RG.Wit.hret RG.Wit.s0 RG.Wit.setup RG.Wit.hpre⟩

end Witness

end FvModexp.Amd64.RequiredGas
