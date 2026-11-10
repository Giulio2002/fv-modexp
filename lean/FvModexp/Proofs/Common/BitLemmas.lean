/-! BitVec facts for the arithmetic the Go compiler emits on non-negative values (signed division by a power of two,
`ASR`/`SBFM` of a value below `2^63`). Used as extra rewrite rules of `janus_run [...]`. -/

namespace FvModexp

theorem getLsbD63_false (x : BitVec 64) (h : x.toNat < 2 ^ 63) : x.getLsbD 63 = false := by
  rw [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow h

theorem asr63_small (x : BitVec 64) (h : x.toNat < 2 ^ 63) :
    ((if x.getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
      x.rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) = 0#64 := by
  have hb := getLsbD63_false x h
  rw [hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_zero,
    Bool.false_and, Bool.false_or, BitVec.getLsbD_rotateRight]
  by_cases h0 : i = 0
  · subst h0
    simp only [Nat.reduceMod, Nat.reduceSub, Nat.zero_lt_one, ite_true, Nat.add_zero, hb, Bool.false_and]
  · have : (1#64).getLsbD i = false := by
      simp [BitVec.getLsbD_one, h0]
    simp [this]

theorem sshiftRight_small (x : BitVec 64) (h : x.toNat < 2 ^ 63) (n : Nat) : x.sshiftRight n = x >>> n := by
  apply BitVec.sshiftRight_eq_of_msb_false
  rw [BitVec.msb_eq_getLsbD_last]; exact getLsbD63_false x h

theorem toInt_small (x : BitVec 64) (h : x.toNat < 2 ^ 63) : x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
theorem rotr_mod (x : BitVec 64) (k : Nat) (hk : 0 < k ∧ k < 64) :
    (x.rotateRight k).toNat % 2 ^ (64 - k) = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_rotateRight, Nat.mod_eq_of_lt (show k < 64 by omega), Nat.or_mod_two_pow]
  have h1 : (x.toNat >>> k) % 2 ^ (64 - k) = x.toNat / 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.mod_eq_of_lt
    have := x.isLt
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add]
    rwa [show 64 - k + k = 64 by omega]
  have h2 : (x.toNat <<< (64 - k) % 2 ^ 64) % 2 ^ (64 - k) = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    exact Nat.mul_mod_left _ _
  rw [h1, h2, Nat.or_zero]

/-- `ASR #k` (an `SBFM`) of a value below `2^63`, in the `toNat` form the executor leaves: `x / 2^k`. -/
theorem asr_small_toNat (x : BitVec 64) (h : x.toNat < 2 ^ 63) (k M Q : Nat) (hk : 0 < k ∧ k < 64)
    (hQ : Q = 2 ^ (64 - k)) :
    ((if x.getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& M |||
      (x.rotateRight k).toNat % Q) = x.toNat / 2 ^ k := by
  rw [getLsbD63_false x h, hQ, rotr_mod x k hk]
  simp

/-- A logical right shift by at least one is non-negative as a signed number. -/
theorem toInt_ushiftRight (x : BitVec 64) (n : Nat) (hn : 0 < n) :
    (x >>> n).toInt = ((x.toNat / 2 ^ n : Nat) : Int) := by
  have h1 : (x >>> n).toNat = x.toNat / 2 ^ n := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : x.toNat / 2 ^ n < 2 ^ 63 := by
    have := x.isLt
    have : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) hn; simpa using this
    have : x.toNat / 2 ^ n ≤ x.toNat / 2 := Nat.div_le_div_left this (by decide)
    omega
  rw [toInt_small _ (by rw [h1]; exact h2), h1]

end FvModexp
