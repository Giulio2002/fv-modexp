/-!
# `ASR #1` of a small non-negative word as the run expands it (arm64; agent infra)

Janus expands `ASR` through `rotateRight`; for `i < 2^63` the low 63 bits of `rotateRight 1` are `i / 2`.
-/

namespace FvModexp.RotA64

theorem rot1_low {i : Nat} (hi : i < 2 ^ 63) :
    ((BitVec.ofNat 64 i).rotateRight 1).toNat % 9223372036854775808 = i / 2 := by
  rw [show (9223372036854775808 : Nat) = 2 ^ 63 from rfl, BitVec.toNat_rotateRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.or_mod_two_pow]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h1 : i * 2 ^ (64 - 1 % 64) % 2 ^ 64 % 2 ^ 63 = 0 := by
    rw [show 64 - 1 % 64 = 63 from rfl, Nat.mod_mod_of_dvd _ (by decide)]
    exact Nat.mul_mod_left _ _
  rw [h1, Nat.or_zero, show 1 % 64 = 1 from rfl, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]

theorem getLsbD63 {i : Nat} (hi : i < 2 ^ 63) : (BitVec.ofNat 64 i).getLsbD 63 = false := by
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_of_lt hi]; rfl

end FvModexp.RotA64
