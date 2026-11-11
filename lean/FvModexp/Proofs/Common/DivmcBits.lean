import Janus

/-!
# Word facts for the code the Go compiler emits around slice expressions (agent divmc)

`z[n:]` keeps the pointer inside the array: the compiler computes `p + 8 * (n & ((n - cap) >>ₛ 63))`
(arm64 `SUB; AND R->63`), i.e. `p + 8n` when `n < cap`, `p` when `n = cap`. Rewrite rules for `janus_run [...]`.
-/

namespace FvModexp

/-- `(x - y) >>ₛ 63` is all ones when `x < y` (and `y - x ≤ 2^63`). -/
theorem sshr63_of_lt (x y : BitVec 64) (h : x.toNat < y.toNat) (hy : y.toNat ≤ 2 ^ 63) :
    ((x - y).sshiftRight 63).toNat = 18446744073709551615 := by
  have hm : (x - y).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
    simp only [Nat.reduceSub, Nat.reducePow, decide_eq_true_eq]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_true hm, BitVec.toNat_not, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_not]
  have : (2 ^ 64 - 1 - (x - y).toNat) / 2 ^ 63 = 0 := by
    rw [BitVec.toNat_sub]; apply Nat.div_eq_of_lt; omega
  rw [this]

/-- `(x - y) >>ₛ 63` is zero when `y ≤ x < 2^63`. -/
theorem sshr63_of_le (x y : BitVec 64) (h : y.toNat ≤ x.toNat) (hx : x.toNat < 2 ^ 63) :
    ((x - y).sshiftRight 63).toNat = 0 := by
  have hm : (x - y).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
    simp only [Nat.reduceSub, Nat.reducePow, decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_sub]
  apply Nat.div_eq_of_lt; omega

theorem and_ones64 (n : Nat) (h : n < 2 ^ 64) : n &&& 18446744073709551615 = n := by
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- `(2^64 - a + b) mod 2^64 = b - a` for `a ≤ b < 2^64` (a 64-bit `SUB`). -/
theorem sub_mod64 (a b : Nat) (h : a ≤ b) (hb : b < 2 ^ 64) :
    (18446744073709551616 - a + b) % 18446744073709551616 = b - a := by omega

theorem mod64_of_lt (a : Nat) (h : a < 2 ^ 64) : a % 18446744073709551616 = a := Nat.mod_eq_of_lt h

/-- amd64 `NEGQ d; SARQ $63, d; ANDQ y, d` (the `z[n:]` pointer mask): `y` when `0 < d ≤ 2^63`. -/
theorem neg_sshr63_and (d y : BitVec 64) (h : 0 < d.toNat) (hd : d.toNat ≤ 2 ^ 63) :
    ((0#64 - d).sshiftRight 63 &&& y) = y := by
  have hm := sshr63_of_lt (0#64) d (by simpa using h) hd
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hm, Nat.and_comm]
  exact and_ones64 _ y.isLt

end FvModexp
