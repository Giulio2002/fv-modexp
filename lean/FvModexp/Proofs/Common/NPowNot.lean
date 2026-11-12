import FvModexp.Proofs.Common.NPowMath

/-!
# `m.isPow2()` fails for a normalised nat `m` that is not a power of two (for `nat.expNN`'s `expNNEven` call)

The loop `for x[i] == 0 { i++ }` (nat.go:381) skips the zero words below the first non-zero one without running
off the end (the top word is non-zero), and the test `i == len(x)-1 && x[i]&(x[i]-1) == 0` (nat.go:384) fails.
-/

set_option autoImplicit false

namespace FvModexp.Expmc

open Janus Janus.Arm64 FvModexp.Exp

/-- a non-zero word `w` with `(w - 1) & w = 0` is a power of two -/
theorem pow2_of_and {w : Nat} (h0 : w ≠ 0) (h : (w - 1) &&& w = 0) : w = 2 ^ Nat.log2 w := by
  have hl := Nat.log2_self_le h0
  have hu : w < 2 ^ (Nat.log2 w + 1) := (Nat.log2_lt h0).1 (Nat.lt_succ_self _)
  refine Nat.le_antisymm (Nat.le_of_not_lt fun hgt => ?_) hl
  have h1 : w - 1 ≠ 0 := by have := Nat.one_le_two_pow (n := Nat.log2 w); omega
  have he : Nat.log2 (w - 1) = Nat.log2 w := (Nat.log2_eq_iff h1).2 ⟨by omega, by omega⟩
  have t1 := Nat.testBit_log2 h1
  have t2 := Nat.testBit_log2 h0
  rw [he] at t1
  have : ((w - 1) &&& w).testBit (Nat.log2 w) = true := by rw [Nat.testBit_and, t1, t2]; rfl
  rw [h, Nat.zero_testBit] at this
  exact absurd this (by decide)

/-- the value of `i` zero words is `0` -/
theorem val_zero_words (M : Memory) (mp : Nat) :
    ∀ i, (∀ j, j < i → M.readLE (mp + 8 * j) 8 = 0) → natVal M mp i = 0
  | 0, _ => rfl
  | i + 1, h => by
    rw [natVal_succ, val_zero_words M mp i (fun j hj => h j (by omega)), h i (by omega), Nat.mul_zero]

/-- one step of the `isPow2` loop on a normalised non-power of two, words `0..i-1` zero: a zero word `i` is not the
top word; a non-zero top word fails the power-of-two test -/
theorem notPow_step (M : Memory) (mp n i : Nat) (hn : 0 < n) (hN : NatNorm M mp n)
    (hnp : ¬∃ k, natVal M mp n = 2 ^ k) (hz : ∀ j, j < i → M.readLE (mp + 8 * j) 8 = 0) (hi : i < n) :
    (M.readLE (mp + 8 * i) 8 = 0 → i + 1 < n) ∧
      (M.readLE (mp + 8 * i) 8 ≠ 0 → i + 1 = n → (M.readLE (mp + 8 * i) 8 - 1) &&& M.readLE (mp + 8 * i) 8 ≠ 0) := by
  refine ⟨fun h0 => ?_, fun h0 hl ha => hnp ?_⟩
  · refine Nat.lt_of_le_of_ne (by omega) fun hl => ?_
    rcases hN with h | h
    · omega
    · exact h (by rw [show n - 1 = i by omega]; exact h0)
  · have hw := pow2_of_and h0 ha
    refine ⟨64 * i + Nat.log2 (M.readLE (mp + 8 * i) 8), ?_⟩
    rw [← hl, natVal_succ, val_zero_words M mp i hz, hw, Nat.log2_two_pow, Nat.pow_add, Nat.zero_add]

end FvModexp.Expmc
