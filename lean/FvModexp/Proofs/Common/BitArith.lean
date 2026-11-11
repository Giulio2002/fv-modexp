import Janus
/-! BitVec facts for Go slice arithmetic (the `(start - cap) >> 63` mask of a re-slice). -/

namespace FvModexp.BitArith


theorem asr63_toNat (x : BitVec 64) : (x.sshiftRight 63).toNat = if x.toNat < 2 ^ 63 then 0 else 2 ^ 64 - 1 := by
  have hx := x.isLt
  cases hm : x.msb
  · have h2 := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
    rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, if_pos (by omega)]
    apply Nat.div_eq_of_lt; omega
  · have h2 := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
    rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_not, if_neg (by omega)]
    have : (2 ^ 64 - 1 - x.toNat) / 2 ^ 63 = 0 := by apply Nat.div_eq_of_lt; omega
    rw [this]

theorem and_asr63 (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    a.toNat &&& ((a - b).sshiftRight 63).toNat = if a.toNat < b.toNat then a.toNat else 0 := by
  rw [asr63_toNat, BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · rw [if_neg (by omega), if_pos h, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt a.isLt]
  · rw [if_pos (by omega), if_neg h, Nat.and_zero]

end FvModexp.BitArith

namespace FvModexp.BitArith

theorem and_asr63_lit (k : Nat) (b : BitVec 64) (hk : k < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    k &&& ((BitVec.ofNat 64 k - b).sshiftRight 63).toNat = if k < b.toNat then k else 0 := by
  have := and_asr63 (BitVec.ofNat 64 k) b (by simp; omega) hb
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega)] at this

end FvModexp.BitArith
