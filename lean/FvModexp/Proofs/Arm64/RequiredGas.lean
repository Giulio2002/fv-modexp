import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk2
import FvModexp.Proofs.Arm64.RequiredGas.Blk3
import FvModexp.Proofs.Arm64.RequiredGas.Fin1
import FvModexp.Proofs.Arm64.RequiredGas.Fin
import FvModexp.Proofs.Arm64.RequiredGas.Head
import FvModexp.Proofs.Arm64.RequiredGas.Wit
import FvModexp.Proofs.Arm64.RequiredGas.Sb
import FvModexp.Proofs.Arm64.RequiredGas.Mv
import FvModexp.Proofs.Arm64.RequiredGas.Og

/-!
# `(*bigModExp).RequiredGas(input []byte) uint64` (arm64), go-ethereum v1.17.10 core/vm/contracts.go:606-646

**Guarantee** (`correctness`). For the Osaka receiver (`eip2565`, `eip7823`, `eip7883` all true) and every input slice, the call
returns (no fault, no panic) with the Go ABI preserved, and for every fork from Fusaka on, when the three length headers pass EIP-7823
(`Spec.LengthsPass`), the `uint64` result is EthLib's `requiredGas fork data (parseLengths data)` with `data` the input bytes.
-/

namespace FvModexp.Arm64.RequiredGas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp.Arm64.RG

theorem run (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') :=
  rg_head sb mv (rg_blk2 sb mv (rg_blk3 sb mv (rg_fin1 (rg_fin2 sb mv og_summary)))) c ptr len cap

/-- **Row 2 (arm64).** `(*bigModExp).RequiredGas` with the Osaka receiver: returns for every input, and when the lengths pass EIP-7823
the result is EthLib's `requiredGas` at every fork from Fusaka on. -/
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544)
      (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) :=
  run c ptr len cap

namespace Witness

/-- **Non-vacuity**: a concrete Osaka-receiver call with 96 zero bytes satisfies the precondition (and returns). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, ptr, len, cap] s ∧
    (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) s s' :=
  ⟨RG.Wit.ret, RG.Wit.s0, _, _, _, _, RG.Wit.hret, RG.Wit.setup, RG.Wit.hpre,
    correctness _ _ _ _ RG.Wit.ret RG.Wit.hret RG.Wit.s0 RG.Wit.setup RG.Wit.hpre⟩

end Witness

end FvModexp.Arm64.RequiredGas
