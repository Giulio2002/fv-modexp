import Janus

/-!
# Go's slice-pointer masking (agent expmc)

`s[i:j]` with a possibly empty result computes the new base as `ptr + (i*8 & mask)` with
`mask = (i - cap) >>s 63` (arm64 `AND Rx->63`, amd64 `NEGQ; SARQ $63; ANDQ`): all ones when the
result is non-empty, zero otherwise. These lemmas evaluate the mask in the non-empty case.
-/

namespace FvModexp

theorem sshr63_allOnes (v : BitVec 64) (h : 2 ^ 63 ≤ v.toNat) : v.sshiftRight 63 = BitVec.allOnes 64 := by
  have hm : v.msb = true := by
    rw [BitVec.msb_eq_decide]; simp; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hr : (BitVec.allOnes 64).getLsbD i = true := by rw [BitVec.getLsbD_allOnes]; simp [hi]
  rw [hr]
  rcases Nat.eq_zero_or_pos i with rfl | hp
  · rw [BitVec.msb_eq_getLsbD_last] at hm; simpa using hm
  · have : ¬ (63 + i < 64) := by omega
    simp [this, show ¬ 64 ≤ i by omega, hm]

/-- `x & mask = x` when the mask word is negative. -/
theorem land_sshr63 (x : Nat) (v : BitVec 64) (hx : x < 2 ^ 64) (h : 2 ^ 63 ≤ v.toNat) :
    x &&& (v.sshiftRight 63).toNat = x := by
  rw [sshr63_allOnes v h, BitVec.toNat_allOnes]
  rw [show (2 : Nat) ^ 64 - 1 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hx

/-- arm64 form: `a & ((a - b) >>s 63) = a` for `a < b < 2^63`. -/
theorem mask_sub_lt (a b : Nat) (h : a < b) (hb : b < 2 ^ 63) :
    a &&& ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).sshiftRight 63).toNat = a :=
  land_sshr63 a _ (by omega) (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)

/-- amd64 form: `x & (-(b - a) >>s 63) = x` for `a < b < 2^63`, `x < 2^64`. -/
theorem mask_neg_sub_lt (x a b : Nat) (hx : x < 2 ^ 64) (h : a < b) (hb : b < 2 ^ 63) :
    x &&& ((0#64 - (BitVec.ofNat 64 b - BitVec.ofNat 64 a)).sshiftRight 63).toNat = x :=
  land_sshr63 x _ hx (by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega)

end FvModexp
