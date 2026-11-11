import FvModexp.Proofs.Common.Calldata
import FvModexp.Proofs.Common.GethGas

/-! `(*bigModExp).RequiredGas` at the `Nat` level (ISA-independent): geth's reading of the input (go-ethereum v1.17.10
core/vm/contracts.go:606-646) and its agreement with EthLib's `requiredGas` when the lengths pass EIP-7823. -/

namespace FvModexp.RgSpec

open Janus.Arm64 EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp Calldata

/-- `uint256.Int.Uint64()`, or `MaxUint64` when `!IsUint64()` (contracts.go:612-623). -/
def sat (v : Nat) : Nat := if v < 2 ^ 64 then v else 2 ^ 64 - 1

/-- geth's `expHead` (contracts.go:626-640): after skipping the 96-byte header (`input[96:]`, empty when `len ≤ 96`), when more than
`baseLen` bytes remain, the big-endian value of `getData(input, baseLen, 32)` if `expLen > 32`, else of `getData(input, baseLen, expLen)`
(zero-padded); otherwise `0`. -/
def expHead (m : Memory) (p len b e : Nat) : Nat :=
  if 96 < len ∧ b < len - 96 then Aux.fromBE (fun i => pad m p len (96 + b + i)) (if 32 < e then 32 else e) else 0

theorem parse (m : Memory) (p len : Nat) :
    parseLengths (Spec.bytesAt m p len) = ⟨word m p len 0, word m p len 32, word m p len 64⟩ := by
  simp only [parseLengths, LENGTH_HEADER_BYTES, readNat_bytesAt]

theorem exponentHead_lt (m : Memory) (p len : Nat) (l : Lengths) : exponentHead (Spec.bytesAt m p len) l < 2 ^ 256 := by
  unfold exponentHead
  rw [readNat_bytesAt]
  have := fromBE_lt (fun i => pad m p len (Lengths.exponentStart l + i)) (min EXPONENT_HEAD_BYTES l.exponent)
    (fun i _ => pad_lt _ _ _ _)
  have h2 : 256 ^ (min EXPONENT_HEAD_BYTES l.exponent) ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (by simp only [EXPONENT_HEAD_BYTES]; omega)
  simp only [Nat.reducePow] at h2 ⊢
  omega

/-- **RequiredGas at the `Nat` level.** -/
theorem gas_eq (fork : Fork) (hf : Spec.PostFusaka fork) (m : Memory) (p len : Nat)
    (hl : Spec.LengthsPass (Spec.bytesAt m p len)) :
    Geth.osakaModexpGas (sat (word m p len 0)) (sat (word m p len 32)) (sat (word m p len 64))
        (expHead m p len (sat (word m p len 0)) (sat (word m p len 32))) =
      requiredGas fork (Spec.bytesAt m p len) (parseLengths (Spec.bytesAt m p len)) := by
  have h := (Spec.lengthsPass_iff _).1 hl
  rw [parse] at h ⊢
  obtain ⟨hb, he, hm⟩ := h
  simp only [MAX_LENGTH_BYTES] at hb he hm
  have sb : sat (word m p len 0) = word m p len 0 := by unfold sat; rw [if_pos (by omega)]
  have se : sat (word m p len 32) = word m p len 32 := by unfold sat; rw [if_pos (by omega)]
  have sm : sat (word m p len 64) = word m p len 64 := by unfold sat; rw [if_pos (by omega)]
  rw [sb, se, sm]
  generalize hB : word m p len 0 = B at *
  generalize hE : word m p len 32 = E at *
  generalize hM : word m p len 64 = M at *
  -- the exponent head
  have hH : expHead m p len B E = exponentHead (Spec.bytesAt m p len) ⟨B, E, M⟩ := by
    unfold exponentHead Lengths.exponentStart
    rw [readNat_bytesAt]
    simp only [BASE_OFFSET, LENGTH_HEADER_BYTES, EXPONENT_HEAD_BYTES]
    unfold expHead
    have hk : (if 32 < E then 32 else E) = min 32 E := by
      by_cases h : 32 < E
      · rw [if_pos h]; omega
      · rw [if_neg h]; omega
    rw [hk]
    split
    · apply fromBE_congr; intro i _; congr 1
    · symm; apply fromBE_zero; intro i _; unfold pad; split <;> omega
  rw [hH]
  have hlt : exponentHead (Spec.bytesAt m p len) ⟨B, E, M⟩ < 2 ^ 256 := by
    unfold exponentHead
    rw [readNat_bytesAt]
    have := fromBE_lt (fun i => pad m p len (Lengths.exponentStart ⟨B, E, M⟩ + i)) (min EXPONENT_HEAD_BYTES E)
      (fun i _ => pad_lt _ _ _ _)
    have h2 : 256 ^ (min EXPONENT_HEAD_BYTES E) ≤ 256 ^ 32 :=
      Nat.pow_le_pow_right (by decide) (by simp only [EXPONENT_HEAD_BYTES]; omega)
    simp only [Nat.reducePow] at h2 ⊢
    omega
  unfold requiredGas
  exact Geth.osaka_gas_eq fork hf B E M _ hb he hm hlt

end FvModexp.RgSpec
