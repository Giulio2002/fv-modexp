import FvModexp.Proofs.Common.RunMath

/-!
# EthLib's `compute` from the machine-level result (ISA independent)

`Run` leaves the result as `n` bytes in memory whose big-endian value is `if m = 0 then 0 else b ^ e % m` (operands read
with `padBE`). This file proves that those bytes ARE EthLib's `compute data (parseLengths data)`:
* `powMod_eq`: EthLib's square-and-multiply `powMod b e m` is `b ^ e % m` (`m > 0`);
* `bytesAt_eq_natToBytes`: `n` memory bytes with big-endian value `v` are `natToBytes n v`;
* `compute_eq`: `compute (bytesAt m p len) (parseLengths …)` is `natToBytes modLen (if m = 0 then 0 else b ^ e % m)` with the
  operands as `padBE` reads.
-/

namespace FvModexp

open Janus Janus.Arm64 EthLib.Base EthLib.Execution.Evm EthLib.Execution.Evm.Precompiles.Modexp

/-- EthLib's `powMod` is modular exponentiation. -/
theorem powMod_eq (b e m : Nat) (_hm : 0 < m) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | ind e ih =>
    rw [powMod]
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [dif_neg h0]
      have hh := ih (e / 2) (by omega) (b * b % m)
      simp only
      rw [hh, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      by_cases ho : e % 2 = 1
      · rw [if_pos ho, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_succ]
        congr 2; omega
      · rw [if_neg ho]; congr 2; omega

/-- The `n` bytes at `q` are the big-endian encoding of their value. -/
theorem bytesAt_eq_natToBytes (m : Memory) (q n : Nat) :
    Spec.bytesAt m q n = ⟨(natToBytes n (beVal m q n)).toArray⟩ := by
  unfold Spec.bytesAt
  congr 1
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, ih, natToBytes_succ, beVal_succ]
    have hb := (m.bytes (q + n)).isLt
    have e1 : (beVal m q n * 256 + (m.bytes (q + n)).toNat) / 256 = beVal m q n := by omega
    have e2 : (beVal m q n * 256 + (m.bytes (q + n)).toNat) % 256 = (m.bytes (q + n)).toNat := by omega
    rw [e1, e2]
    rfl

/-- EthLib's `compute` on call data in memory: the modulus length's big-endian bytes of `b ^ e mod m` (`0` for `m = 0`),
the operands read as `padBE` at the header offsets. -/
theorem compute_eq (m : Memory) (p len : Nat) :
    compute (Spec.bytesAt m p len) (parseLengths (Spec.bytesAt m p len)) =
      let l := parseLengths (Spec.bytesAt m p len)
      let B := padBE m p len 96 l.base
      let E := padBE m p len (96 + l.base) l.exponent
      let M := padBE m p len (96 + l.base + l.exponent) l.modulus
      ⟨(natToBytes l.modulus (if M = 0 then 0 else B ^ E % M)).toArray⟩ := by
  simp only [compute, readNat_eq_padBE, Lengths.exponentStart, Lengths.modulusStart, BASE_OFFSET, LENGTH_HEADER_BYTES,
    Nat.reduceMul]
  split <;> rename_i hM
  · simp only [hM, if_true]
  · rw [powMod_eq _ _ _ (Nat.pos_of_ne_zero hM)]; try simp only [hM, if_false]

end FvModexp
