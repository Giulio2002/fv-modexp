import Janus

/-! Byte-level facts about the Janus arm64 memory model: the bytes of a little-endian read. -/

namespace FvModexp.Bytes

open Janus.Arm64

/-- Byte `j` of the little-endian `k`-byte read at `a` is the memory byte at `a + j`. -/
theorem byte_readLE (m : Memory) (a k j : Nat) (h : j < k) :
    BitVec.ofNat 8 (m.readLE a k / 256 ^ j) = m.bytes (a + j) := by
  induction k generalizing a j with
  | zero => omega
  | succ k ih =>
    rw [Memory.readLE_succ]
    cases j with
    | zero =>
      apply BitVec.eq_of_toNat_eq
      have := (m.bytes a).isLt
      simp only [BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one, Nat.add_zero]
      omega
    | succ j =>
      have e : ((m.bytes a).toNat + 256 * m.readLE (a + 1) k) / 256 ^ (j + 1) = m.readLE (a + 1) k / 256 ^ j := by
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1
        have := (m.bytes a).isLt
        omega
      rw [e, ih (a + 1) j (by omega), show a + 1 + j = a + (j + 1) by omega]

theorem byte_readLE_at (m : Memory) (a k x b : Nat) (h1 : b ≤ x) (h2 : x < b + k) :
    BitVec.ofNat 8 (m.readLE a k / 256 ^ (x - b)) = m.bytes (a + (x - b)) :=
  byte_readLE m a k (x - b) (by omega)

theorem readLE_mod64 (m : Memory) (a k : Nat) (hk : k ≤ 8) : m.readLE a k % 18446744073709551616 = m.readLE a k := by
  apply Nat.mod_eq_of_lt
  have h1 := Memory.readLE_lt m a k
  have h2 : 256 ^ k ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hk
  simp only [Nat.reducePow] at h2
  omega

end FvModexp.Bytes
