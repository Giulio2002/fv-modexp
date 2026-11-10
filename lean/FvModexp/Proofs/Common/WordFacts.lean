import FvModexp.Proofs.Common.DivWW
/-!
# Bridging facts for the word-level models

* `reciprocalWord_eq_div64`: arith.go:333-338 computes the reciprocal with `bits.Div(^u, _M, u)` (`div64`, the software
  `bits.Div64` on arm64 / `DIVQ` on amd64); the model `reciprocalWord` (DivWW.lean) is the exact quotient. They agree
  (`^u < u` because `u` is normalised, so `bits.Div` does not panic).
* `length_le_of_val_lt`: a normalised limb list is no longer than any `k` with `val < 2^(64k)` (length bounds of results
  from value bounds — used for slice-capacity side conditions).
-/
namespace FvModexp.Mdl

theorem reciprocalWord_eq_div64 (d1 : Nat) (h0 : 0 < d1) (h : d1 < 2 ^ 64) :
    reciprocalWord d1 =
      (div64 (2 ^ 64 - 1 - d1 * 2 ^ nlz d1 % 2 ^ 64) (2 ^ 64 - 1) (d1 * 2 ^ nlz d1 % 2 ^ 64)).1 := by
  obtain ⟨_, hs1, hs2⟩ := nlz_spec d1 h0 h
  unfold reciprocalWord
  simp only []
  rw [Nat.mod_eq_of_lt hs1]
  generalize d1 * 2 ^ nlz d1 = u at *
  rw [div64_spec _ _ u (by omega) (by omega) (by omega) (by omega)]

theorem length_le_of_val_lt {l : List Nat} (hw : Wd l) (hn : Normed l) {k : Nat} (h : val l < 2 ^ (64 * k)) :
    l.length ≤ k := by
  refine Nat.le_of_not_lt (fun hlt => ?_)
  have hne : l ≠ [] := by intro e; subst e; simp at hlt
  have := Normed.val_ge hn hne hw
  have : 2 ^ (64 * k) ≤ 2 ^ (64 * (l.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end FvModexp.Mdl
