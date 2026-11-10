import FvModexp.Proofs.Common.Conv
import FvModexp.Spec

/-!
# The call-data reads of `Run` as numbers (ISA independent)

`padBE m p len start n`: the `n` bytes of the call data `(p, len)` from `start`, read big-endian, zero past `len`
(EIP-198 "infinitely right-padded"). `readNat_eq_padBE` bridges it to EthLib's `readNat (bytesAt m p len) start n`.
-/

namespace FvModexp

open Janus Janus.Arm64 EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp

/-- Byte `j` of the call data `(p, len)`, zero past its end. -/
def padByte (m : Memory) (p len j : Nat) : Nat := if j < len then (m.bytes (p + j)).toNat else 0

/-- The `n` call-data bytes from `start`, big-endian. -/
def padBE (m : Memory) (p len start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => padBE m p len start n * 256 + padByte m p len (start + n)

theorem foldl_acc' (a : Nat) (L : List UInt8) :
    L.foldl (fun acc b => acc * 256 + b.toNat) a = a * 256 ^ L.length + L.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction L generalizing a with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b.toNat), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ L.length)]
    omega

theorem byteAt_bytesAt_toNat (m : Memory) (p len j : Nat) :
    (byteAt (Spec.bytesAt m p len) j).toNat = padByte m p len j := by
  rw [Spec.byteAt_bytesAt, padByte]
  split
  · simp only [Spec.byteOf]
    have := (m.bytes (p + j)).isLt
    simp [UInt8.toNat, UInt8.ofNat]
  · rfl

/-- EthLib's padded read is `padBE`. -/
theorem readNat_eq_padBE (m : Memory) (p len start n : Nat) :
    readNat (Spec.bytesAt m p len) start n = padBE m p len start n := by
  unfold readNat EthLib.Execution.Evm.bufferRead bytesToNat
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [padBE, byteAt_bytesAt_toNat]

/-- Inside the data, `padBE` is the plain big-endian read. -/
theorem padBE_inside (m : Memory) (p len start n : Nat) (h : start + n ≤ len) :
    padBE m p len start n = beVal m (p + start) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [padBE, beVal_succ, ih (by omega), padByte, if_pos (by omega), Nat.add_assoc]

/-- Past the end every byte is zero. -/
theorem padBE_past (m : Memory) (p len start n : Nat) (h : len ≤ start) : padBE m p len start n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [padBE, ih, padByte, if_neg (by omega)]

/-- A buffer holding the call-data bytes `[start, len)` then zeros (Go's `RightPadBytes` copy): its big-endian value
is the padded read. -/
theorem beVal_padded (mb : Memory) (m : Memory) (buf p len start n : Nat)
    (hcopy : ∀ j, j < n → (mb.bytes (buf + j)).toNat = padByte m p len (start + j)) :
    beVal mb buf n = padBE m p len start n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [beVal_succ, padBE, ih (fun j hj => hcopy j (by omega)), hcopy n (by omega)]

end FvModexp
