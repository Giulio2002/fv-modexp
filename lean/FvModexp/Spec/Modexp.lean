import Janus
import EthLib.Execution.Evm.Precompiles.Modexp
import FvModexp.Spec.Mem

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): plain definitions for the statements about geth's `(*bigModExp)` methods.
The reference semantics itself (`modexp`, `chargedGas`, `requiredGas`, `compute`, `checkLengths`, `parseLengths`) is EthLib's, used unchanged. -/

namespace FvModexp.Spec

open Janus.Arm64
open EthLib.Execution.Evm.Precompiles.Modexp

/-- The call data passes the EIP-7823 bound: `checkLengths (parseLengths data)` succeeds (every length header is at most 1024). -/
def LengthsPass (data : ByteArray) : Prop := checkLengths (parseLengths data) = Except.ok ()

/-- The call data violates the EIP-7823 bound. -/
def LengthsFail (data : ByteArray) : Prop := ¬ LengthsPass data

/-- The Osaka receiver: the three `bool` fields `eip2565`, `eip7823`, `eip7883` of `*bigModExp` at address `p` are all `true` (byte value 1).
Go keeps a `bool` as a byte that is 0 or 1; geth builds exactly this value for `PrecompiledContractsOsaka[0x05]` (and for the later forks that reuse the set). -/
def OsakaReceiver (m : Memory) (p : Nat) : Prop :=
  (m.bytes p).toNat = 1 ∧ (m.bytes (p + 1)).toNat = 1 ∧ (m.bytes (p + 2)).toNat = 1

/-- The result `uint64` of a Go call, as a natural number (`X0` on arm64, `RAX` on amd64): the value of the register. -/
def u64 (x : BitVec 64) : Nat := x.toNat

theorem lengthsPass_iff (data : ByteArray) :
    LengthsPass data ↔ (parseLengths data).base ≤ MAX_LENGTH_BYTES ∧ (parseLengths data).exponent ≤ MAX_LENGTH_BYTES ∧
      (parseLengths data).modulus ≤ MAX_LENGTH_BYTES := by
  unfold LengthsPass checkLengths
  by_cases h1 : (parseLengths data).base > MAX_LENGTH_BYTES
  · simp [h1] <;> omega
  · by_cases h2 : (parseLengths data).exponent > MAX_LENGTH_BYTES
    · simp [h1, h2] <;> omega
    · by_cases h3 : (parseLengths data).modulus > MAX_LENGTH_BYTES
      · simp [h1, h2, h3] <;> omega
      · simp [h1, h2, h3] <;> omega

end FvModexp.Spec
