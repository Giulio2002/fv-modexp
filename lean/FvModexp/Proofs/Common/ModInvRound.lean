import FvModexp.Proofs.Common.ModInvMath

/-!
# `nat.modularInverseModPowerOfTwo`: the loop invariant as a congruence (agent infra)

The machine loop (nat.go:1325-1332) is tracked by the invariant `x · z ≡ 1 (mod 2^(2^j · 32))` at round `j`
(`i = 2^j`): it holds after `z.setWord(k0)` (`z0_inv`), each round doubles the exponent (`round_inv`), and after the
final round (`numWords ≤ 2^j`) the result is below `2^n` and inverts `x` mod `2^n`, so it is the model's value
(`final_val`, by uniqueness of the inverse).
-/

namespace FvModexp.Exp

open Janus Janus.Arm64

/-- `x · z0 ≡ 1 (mod 2^64)` when `z0`'s low word is Newton's `k0` -/
theorem z0_inv (x z0 : Nat) (hx : x % 2 = 1) (hz0 : z0 % B = newton 64 (x % B)) :
    x * z0 % 2 ^ (2 ^ 1 * 32) = 1 % 2 ^ (2 ^ 1 * 32) := by
  have hx0 : x % B % 2 = 1 := by
    rw [B_def, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 64))]; exact hx
  have hxB : x % B < B := Nat.mod_lt _ B_pos
  have hN := newtonLoop_spec 64 (x % B) hxB (by omega) 64 0
    ((x % B + B - 1) % B) ((2 + B - x % B % B) % B) (by simp) (newton_init (x % B) hx0 hxB) (by
      have hB : B = 18446744073709551616 := B_eq
      have : (x % B + B - 1) % B = x % B - 1 := by rw [hB] at hxB ⊢; omega
      rw [this]; simp; omega)
  have hB64 : (2 : Nat) ^ (2 ^ 1 * 32) = B := by rw [B_def]
  have hz0' : z0 % B = newton 64 (x % B) % B := by
    rw [hz0]; exact (Nat.mod_eq_of_lt (by unfold newton; exact newton_lt _ _ _ _ (Nat.mod_lt _ B_pos))).symm
  rw [hB64, Nat.mul_mod, hz0', Nat.mul_mod (x % B), Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
  have hN' : x % B * newtonLoop 64 0 ((x % B + B - 1) % B) ((2 + B - x % B % B) % B) % 2 ^ 64 = 1 % 2 ^ 64 := by
    simpa using hN
  unfold newton
  rw [← B_def] at hN'
  rw [Nat.mul_mod] at hN' ⊢; simp only [Nat.mod_mod] at hN' ⊢; exact hN'

/-- one Hensel round (`i = 2^j`) doubles the exponent of the congruence -/
theorem round_inv (x z j : Nat) (hz : x * z % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    x * subMod2N (z * 2) (z * z % 2 ^ (2 ^ j * 64) * (x % B ^ min (2 ^ j) (nlen x)) % 2 ^ (2 ^ j * 64))
      (2 ^ j * 64) % 2 ^ (2 ^ (j + 1) * 32) = 1 % 2 ^ (2 ^ (j + 1) * 32) := by
  have e : 2 ^ (j + 1) * 32 = 2 ^ j * 64 := by rw [Nat.pow_succ]; omega
  rw [e]
  exact hensel_step x z (2 ^ j * 32) (2 ^ j * 64) _ (xs_mod x (2 ^ j)) hz (by omega)

/-- a congruence `x · z ≡ 1` modulo a power `≥ 2` makes `z` odd, in particular non-zero -/
theorem odd_of_inv {x z a : Nat} (ha : 1 ≤ a) (hz : x * z % 2 ^ a = 1 % 2 ^ a) : z % 2 = 1 := by
  have h2 : 2 ∣ 2 ^ a := Nat.pow_dvd_pow_iff_le_right'.2 ha |> fun h => by simpa using h
  have := congrArg (· % 2) hz
  simp only [Nat.mod_mod_of_dvd _ h2] at this
  rw [Nat.mul_mod] at this
  rcases Nat.mod_two_eq_zero_or_one z with h | h
  · rw [h] at this; simp at this
  · exact h

/-- the final round (`numWords ≤ 2^j`, `64 < n`) computes the model's value -/
theorem final_val (x z n j : Nat) (hx : x % 2 = 1) (hn : 64 < n) (hj : (n + 63) / 64 ≤ 2 ^ j)
    (hz : x * z % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    subMod2N (z * 2) (z * z % 2 ^ n * (x % B ^ min ((n + 63) / 64) (nlen x)) % 2 ^ n) n =
      modularInverseModPowerOfTwo x n := by
  have h1 : x * subMod2N (z * 2) (z * z % 2 ^ n * (x % B ^ min ((n + 63) / 64) (nlen x)) % 2 ^ n) n % 2 ^ n =
      1 % 2 ^ n := by
    apply hensel_step x z (2 ^ j * 32) n _ _ hz
    · have : 2 ^ j * 32 * 2 = 2 ^ j * 64 := by omega
      omega
    · have hnw : n ≤ (n + 63) / 64 * 64 := by omega
      have hd : 2 ^ n ∣ 2 ^ ((n + 63) / 64 * 64) := Nat.pow_dvd_pow 2 hnw
      rw [← Nat.mod_mod_of_dvd _ hd, xs_mod, Nat.mod_mod_of_dvd _ hd]
  have h3 := modularInverseModPowerOfTwo_spec x n hx (by omega)
  have h4 : modularInverseModPowerOfTwo x n < 2 ^ n := by
    unfold modularInverseModPowerOfTwo; split
    · omega
    · exact (subMod2N_spec _ _ _).1
  exact inv_unique (subMod2N_spec _ _ _).1 h4 h1 h3

end FvModexp.Exp
