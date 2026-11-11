import FvModexp.Proofs.Common.Util
import FvModexp.Spec

/-! The EthLib call-data reads (`readNat`, zero past the end) on `Spec.bytesAt` as big-endian sums of memory bytes. -/

namespace FvModexp.Calldata

open Janus.Arm64 EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp

/-- Byte `j` of the call data `(p, len)`, zero past its end ("infinitely right-padded with zero bytes"). -/
def pad (m : Memory) (p len j : Nat) : Nat := if j < len then (m.bytes (p + j)).toNat else 0

theorem fromBE_congr {f g : Nat → Nat} (n : Nat) (h : ∀ i, i < n → f i = g i) : Aux.fromBE f n = Aux.fromBE g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [Aux.fromBE]
    rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem foldl_acc (a : Nat) (L : List UInt8) :
    L.foldl (fun acc b => acc * 256 + b.toNat) a = a * 256 ^ L.length + L.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction L generalizing a with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b.toNat), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ L.length)]
    omega

theorem bytesToNat_cons (b : UInt8) (L : List UInt8) : bytesToNat (b :: L) = b.toNat * 256 ^ L.length + bytesToNat L := by
  simp only [bytesToNat, List.foldl_cons]
  rw [foldl_acc]
  simp

theorem byteOf_toNat (m : Memory) (a : Nat) : (Spec.byteOf m a).toNat = (m.bytes a).toNat := by
  simp only [Spec.byteOf]
  have := (m.bytes a).isLt
  simp [UInt8.toNat, UInt8.ofNat]

theorem readNat_bytesAt (m : Memory) (p len start size : Nat) :
    readNat (Spec.bytesAt m p len) start size = Aux.fromBE (fun i => pad m p len (start + i)) size := by
  unfold readNat EthLib.Execution.Evm.bufferRead
  induction size generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, bytesToNat_cons, Aux.fromBE]
    have e : (List.map ((fun i => byteAt (Spec.bytesAt m p len) (start + i)) ∘ Nat.succ) (List.range n)) =
        List.map (fun i => byteAt (Spec.bytesAt m p len) (start + 1 + i)) (List.range n) := by
      apply List.map_congr_left; intro i _; simp only [Function.comp]; congr 1; omega
    rw [e, ih (start + 1), List.length_map, List.length_range]
    congr 1
    · rw [Spec.byteAt_bytesAt, pad]
      simp only [Nat.add_zero]
      split <;> simp [byteOf_toNat]
    · apply fromBE_congr; intro i _; congr 1; omega

theorem pad_lt (m : Memory) (p len j : Nat) : pad m p len j < 256 := by
  unfold pad; split
  · exact (m.bytes (p + j)).isLt
  · omega

theorem fromBE_lt (f : Nat → Nat) (n : Nat) (h : ∀ i, i < n → f i < 256) : Aux.fromBE f n < 256 ^ n := by
  induction n generalizing f with
  | zero => simp [Aux.fromBE]
  | succ n ih =>
    simp only [Aux.fromBE]
    have h0 := h 0 (by omega)
    have h1 := ih (fun i => f (i + 1)) (fun i hi => h (i + 1) (by omega))
    have : f 0 * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.pow_succ]; omega

theorem fromBE_zero (f : Nat → Nat) (n : Nat) (h : ∀ i, i < n → f i = 0) : Aux.fromBE f n = 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [Aux.fromBE, h 0 (by omega), Nat.zero_mul, Nat.zero_add]
    exact ih _ (fun i hi => h (i + 1) (by omega))

/-- The call-data word at `start` (32 bytes, zero-padded). -/
abbrev word (m : Memory) (p len start : Nat) : Nat := Aux.fromBE (fun i => pad m p len (start + i)) 32

theorem word_lt (m : Memory) (p len start : Nat) : word m p len start < 2 ^ 256 := by
  have := fromBE_lt (fun i => pad m p len (start + i)) 32 (fun i _ => pad_lt _ _ _ _)
  simpa using this

/-- `uint256.Int.Uint64()` capped at `MaxUint64` unless `IsUint64()` (contracts.go:612-623), from the limbs. -/
theorem sat_limbs (l0 l1 l2 l3 : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64) :
    (if l3 ||| (l2 ||| l1) = 0 then l0 else 2 ^ 64 - 1) =
      (if l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3 < 2 ^ 64 then l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3
        else 2 ^ 64 - 1) := by
  simp only [Nat.or_eq_zero_iff]
  by_cases h : l3 = 0 ∧ l2 = 0 ∧ l1 = 0
  · obtain ⟨a, b, c⟩ := h; subst a b c; simp [h0]
  · rw [if_neg h, if_neg]
    intro hc; apply h
    refine ⟨?_, ?_, ?_⟩ <;> (apply Classical.byContradiction; intro hne; have := Nat.pos_of_ne_zero hne
                             simp only [Nat.reducePow] at *; omega)

end FvModexp.Calldata
