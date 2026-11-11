import Janus

/-! `LSL #3` (`UBFM`) as the arm64 executor leaves it, on a literal operand (agent divmc). -/

namespace FvModexp

theorem lsl3_ofNat (n : Nat) (hn : 8 * n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64) =
      BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  have h := Janus.Contracts.Iface.lsl_toNat (BitVec.ofNat 64 n) 3 (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_and]
  change (_ &&& 18446744073709551608) &&& 18446744073709551615 = _
  rw [show (64 - 3 : Nat) = 61 from rfl, show (2 ^ 64 - 2 ^ 3 : Nat) = 18446744073709551608 from rfl] at h
  rw [h, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  have : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_mod]

end FvModexp
