import FvModexp.Proofs.Common.ExpEven

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo`'s model is THE inverse in `[0, 2^n)` (agent infra, red-team s42)

`modularInverseModPowerOfTwo_spec` gives the congruence `x · r ≡ 1 (mod 2^n)`; with the range fact below the value
stated by `ModInv.ens` is the unique such `r`, i.e. the mathematical `x⁻¹ mod 2^n`.
-/

namespace FvModexp.Exp

theorem modularInverseModPowerOfTwo_lt (x n : Nat) : modularInverseModPowerOfTwo x n < 2 ^ n := by
  unfold modularInverseModPowerOfTwo
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos n)
  · exact (subMod2N_spec _ _ _).1

/-- uniqueness: any `r < 2^n` with `x · r ≡ 1 (mod 2^n)` is the model's value (odd `x`, `0 < n`) -/
theorem modularInverseModPowerOfTwo_unique (x n r : Nat) (hx : x % 2 = 1) (hn : 0 < n) (hr : r < 2 ^ n)
    (h : x * r % 2 ^ n = 1 % 2 ^ n) : modularInverseModPowerOfTwo x n = r := by
  have h1 := modularInverseModPowerOfTwo_spec x n hx hn
  have h2 := modularInverseModPowerOfTwo_lt x n
  generalize modularInverseModPowerOfTwo x n = v at h1 h2
  -- x is invertible mod 2^n: multiply both congruences by v resp. r
  have e : v % 2 ^ n = r % 2 ^ n := by
    have hv : r * (x * v) % 2 ^ n = r % 2 ^ n := by
      rw [Nat.mul_mod, h1, ← Nat.mul_mod, Nat.mul_one]
    have hr' : v * (x * r) % 2 ^ n = v % 2 ^ n := by
      rw [Nat.mul_mod, h, ← Nat.mul_mod, Nat.mul_one]
    rw [← hv, ← hr']
    congr 1
    rw [Nat.mul_left_comm v x r, Nat.mul_left_comm r x v, Nat.mul_comm v r]
  rwa [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hr] at e

end FvModexp.Exp
