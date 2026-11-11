import FvModexp.Proofs.Common.ExpMont

/-!
# The final reduction of the Montgomery windows (nat.go:1478-1488 / 1690-1698), ISA-independent

`zz = zz.montgomery(z, one, …)` with `one = 1` gives `zz ≤ m` (Montgomery reduction of `z · 1` with `z < B^n`), so after
`if zz.cmp(m) >= 0 { zz = zz.sub(zz, m) … }` the difference is `0` and the `div` fallback (`zz.cmp(m) >= 0` again) is never
reached.
-/

namespace FvModexp.Exp

theorem mont_one_le (n x m k : Nat) (hn : 1 ≤ n) (hx : x < B ^ n) (hm : m < B ^ n) (hk : (k * m + 1) % B = 0) :
    montgomery n x 1 m k ≤ m := by
  have h1 : 1 < B ^ n := by
    have : B ^ 1 ≤ B ^ n := Nat.pow_le_pow_right B_pos hn
    have hB := B_eq; rw [Nat.pow_one] at this; omega
  obtain ⟨Q, T, hQ, hT, _, he⟩ := montgomery_spec n x 1 m k hn hx h1 hm hk
  have h2 : Q * m ≤ (B ^ n - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h3 : T * B ^ n < (m + 1) * B ^ n := by
    rw [hT, Nat.mul_one]
    have : (B ^ n - 1) * m + B ^ n ≤ (m + 1) * B ^ n := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm (B ^ n) m]
      omega
    omega
  have hTm : T ≤ m := by have := Nat.lt_of_mul_lt_mul_right h3; omega
  rw [he, if_neg (show ¬ B ^ n ≤ T by omega)]
  exact hTm

end FvModexp.Exp
