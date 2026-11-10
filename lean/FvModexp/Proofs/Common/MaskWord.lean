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

namespace FvModexp

/-- The arm64 `AND Rm->63` (an arithmetic shift by 63 decoded as `SBFM`) in the form the executor leaves it:
all ones when `a < b < 2^63`, so masking `x` keeps `x`. -/
theorem asr63_mask (a b x : Nat) (h : a < b) (hb : b < 2 ^ 63) (hx : x < 2 ^ 64) :
    (((if (BitVec.ofNat 64 a - BitVec.ofNat 64 b).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&&
        18446744073709551614 ||| ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).rotateRight 63).toNat % 2) &&& x) = x := by
  have hv : 2 ^ 63 ≤ (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have h63 : (BitVec.ofNat 64 a - BitVec.ofNat 64 b).getLsbD 63 = true := by
    rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hr : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).rotateRight 63).toNat % 2 = 1 := by
    have h0 : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).rotateRight 63).getLsbD 0 = true := by
      rw [BitVec.getLsbD_rotateRight]; simpa using h63
    rw [BitVec.getLsbD, Nat.testBit_zero] at h0
    exact of_decide_eq_true h0
  rw [if_pos h63, hr]
  have : ((18446744073709551615#64).toNat &&& 18446744073709551614 ||| 1 : Nat) = 2 ^ 64 - 1 := by decide
  rw [this, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

end FvModexp

namespace FvModexp

/-- amd64 form (mask on the left): `((a - b) >>s 63) & x = x` for `a < b < 2^63`. -/
theorem sshr_land_lt (a b x : Nat) (h : a < b) (hb : b < 2 ^ 63) (hx : x < 2 ^ 64) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).sshiftRight 63).toNat &&& x = x := by
  rw [Nat.and_comm]
  exact land_sshr63 x _ hx (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)

theorem two_sub_one (n : Nat) (h : n < 2 ^ 62) :
    BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega

end FvModexp

namespace FvModexp

theorem neg_sshr_land_lt (x a b : Nat) (hx : x < 2 ^ 64) (h : a < b) (hb : b < 2 ^ 63) :
    ((0#64 - (BitVec.ofNat 64 b - BitVec.ofNat 64 a)).sshiftRight 63).toNat &&& x = x := by
  rw [Nat.and_comm]; exact mask_neg_sub_lt x a b hx h hb

end FvModexp

namespace FvModexp

theorem toInt_add_self (n : Nat) (h : n + n < 2 ^ 63) :
    BitVec.toInt (BitVec.ofNat 64 n + BitVec.ofNat 64 n) = ((n + n : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have : (BitVec.ofNat 64 n + BitVec.ofNat 64 n).toNat = n + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [this]; split <;> omega

end FvModexp
