import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.Conv

/-!
# The words of a normalised nat `m = 2^k` (for `m.isPow2()` in `nat.expNN`)
-/

namespace FvModexp.Expmc

open Janus Janus.Arm64 FvModexp.Exp

theorem pow_mod64 (a : Nat) : 2 ^ a % 2 ^ 64 = if a < 64 then 2 ^ a else 0 := by
  split
  · exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by assumption))
  · exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))

/-- a normalised `n`-word nat of value `2^k`: `k = 64 (n-1) + e` with `e < 64`, words `0..n-2` zero, top word `2^e` -/
theorem pow_words (M : Memory) (mp n k : Nat) (hn : 0 < n) (hv : natVal M mp n = 2 ^ k) (hN : NatNorm M mp n) :
    64 * (n - 1) ≤ k ∧ k < 64 * n ∧
      ∀ i, i < n → M.readLE (mp + 8 * i) 8 = if i + 1 = n then 2 ^ (k - 64 * (n - 1)) else 0 := by
  have hw : ∀ i, i < n → M.readLE (mp + 8 * i) 8 = 2 ^ k / 2 ^ (64 * i) % 2 ^ 64 := by
    intro i hi
    have := readLE_win M mp i 1 n (by omega)
    rw [Nat.mul_one] at this
    rw [this]; unfold win; unfold natVal at hv
    rw [hv, B_def, Nat.pow_one, ← Nat.pow_mul]
  have hlt : k < 64 * n := by
    have h := readLE_lt_B M mp n
    unfold natVal at hv
    rw [hv, B_def, ← Nat.pow_mul] at h
    exact (Nat.pow_lt_pow_iff_right (by decide)).1 h
  have hge : 64 * (n - 1) ≤ k := by
    rcases hN with h | h
    · omega
    · rw [hw (n - 1) (by omega)] at h
      refine Nat.le_of_not_lt fun hc => h ?_
      rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) hc)]
  refine ⟨hge, hlt, fun i hi => ?_⟩
  rw [hw i hi, Nat.pow_div (by omega) (by decide), pow_mod64]
  split <;> split <;> first | rfl | (exfalso; omega) | (congr 1; omega)

end FvModexp.Expmc
