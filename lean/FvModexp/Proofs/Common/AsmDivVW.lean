import Janus
import FvModexp.Proofs.Common.AsmDivMath
import FvModexp.Proofs.Common.AsmDivNat

/-!
# Word-by-word long division (`divWVW`, go-bigmodexpfix `src/math/big/natdiv.go:579`): the loop arithmetic

```go
func divWVW(z []Word, xn Word, x []Word, y Word) (r Word) {
	r = xn
	if len(x) == 1 { qq, rr := bits.Div(uint(r), uint(x[0]), uint(y)); z[0] = Word(qq); return Word(rr) }
	rec := reciprocalWord(y)
	for i := len(z) - 1; i >= 0; i-- { z[i], r = divWW(r, x[i], y, rec) }
	return r
}
```
With `n = len z = len x` and `k` limbs still to divide (`i = k - 1`), the running prefix is
`H k = xn·B^(n-k) + x[k:n]` (`B = 2^64`); the loop keeps `r = H k % y` and `z[k:n] = H k / y`. One step:
`H (k-1) = H k · B + x[k-1]` (`H_step`), the new digit is `(r·B + x[k-1]) / y < B` (`digit_lt`) and
`H(k-1) / y = (H k / y)·B + digit`, `H(k-1) % y = (r·B + x[k-1]) % y` (`dstep`). At `k = n`, `H = xn`; at `k = 0`,
`H = xn·B^n + x` (the dividend).
-/

open Janus Janus.Arm64

namespace FvModexp.AsmDivVW

/-- the running prefix `xn·B^(n-k) + x[k:n]` (`x` = the `n` limbs at `xp` in `m`) -/
def H (m : Memory) (xn xp n k : Nat) : Nat := xn * 2 ^ (64 * (n - k)) + m.readLE (xp + 8 * k) (8 * (n - k))

theorem H_top (m : Memory) (xn xp n : Nat) : H m xn xp n n = xn := by
  simp [H]

theorem H_zero (m : Memory) (xn xp n : Nat) : H m xn xp n 0 = xn * 2 ^ (64 * n) + m.readLE xp (8 * n) := by
  simp [H]

theorem H_step (m : Memory) (xn xp n k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) :
    H m xn xp n (k - 1) = H m xn xp n k * 2 ^ 64 + m.readLE (xp + 8 * (k - 1)) 8 := by
  unfold H
  rw [show 8 * (n - (k - 1)) = 8 + 8 * (n - k) by omega, Memory.readLE_add,
    show xp + 8 * (k - 1) + 8 = xp + 8 * k by omega, show 64 * (n - (k - 1)) = 64 * (n - k) + 64 by omega,
    Nat.pow_add, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]
  generalize m.readLE (xp + 8 * k) (8 * (n - k)) = A
  generalize m.readLE (xp + 8 * (k - 1)) 8 = d
  generalize 2 ^ (64 * (n - k)) = P
  rw [Nat.add_mul, Nat.mul_assoc]; ac_rfl

theorem digit_lt (r x y : Nat) (hr : r < y) (hx : x < 2 ^ 64) : (r * 2 ^ 64 + x) / y < 2 ^ 64 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : (r + 1) * 2 ^ 64 ≤ y * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at this; omega

theorem dstep (Hk x y : Nat) (hy : 0 < y) :
    (Hk * 2 ^ 64 + x) / y = Hk / y * 2 ^ 64 + (Hk % y * 2 ^ 64 + x) / y ∧
    (Hk * 2 ^ 64 + x) % y = (Hk % y * 2 ^ 64 + x) % y := by
  have e : Hk * 2 ^ 64 + x = (Hk % y * 2 ^ 64 + x) + y * (Hk / y * 2 ^ 64) := by
    conv => lhs; rw [← Nat.mod_add_div Hk y]
    rw [Nat.add_mul, Nat.mul_assoc]; omega
  rw [e, Nat.add_mul_div_left _ _ hy, Nat.add_mul_mod_self_left]
  exact ⟨by omega, rfl⟩

/-- the quotient limbs `z[k-1:n]` after storing digit `d` at `z[k-1]` -/
theorem q_store (m : Memory) (zp n k d : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (m.writeLE (zp + 8 * (k - 1)) 8 d).readLE (zp + 8 * (k - 1)) (8 * (n - (k - 1))) =
      d % 2 ^ 64 + 2 ^ 64 * m.readLE (zp + 8 * k) (8 * (n - k)) := by
  rw [show 8 * (n - (k - 1)) = 8 + 8 * (n - k) by omega, Memory.readLE_add, Memory.readLE_writeLE_self,
    show zp + 8 * (k - 1) + 8 = zp + 8 * k by omega, Memory.readLE_writeLE_of_disjoint (m := m) _ (by omega)]

/-- the invariant step: `r = H k % y`, `Q = H k / y` give the next remainder/quotient -/
theorem inv_step (Hk Q r x y : Nat) (hy : 0 < y) (hr : r = Hk % y) (hQ : Q = Hk / y) :
    (r * 2 ^ 64 + x) / y + 2 ^ 64 * Q = (Hk * 2 ^ 64 + x) / y ∧ (r * 2 ^ 64 + x) % y = (Hk * 2 ^ 64 + x) % y := by
  obtain ⟨h1, h2⟩ := dstep Hk x y hy
  subst hr hQ
  rw [h1, h2]; exact ⟨by ac_rfl, rfl⟩

/-- the inlined/called `reciprocalWord`: `((2^64-1-U)·2^64 + 2^64-1) / U = (2^128-1)/U - 2^64` for normalised `U` -/
theorem recip_val (U : Nat) (h1 : 2 ^ 63 ≤ U) (h2 : U < 2 ^ 64) :
    ((18446744073709551615 - U) * 18446744073709551616 + 18446744073709551615) / U = (2 ^ 128 - 1) / U - 2 ^ 64 := by
  have e : (18446744073709551615 - U) * 18446744073709551616 + 18446744073709551615 = (2 ^ 128 - 1) - U * 2 ^ 64 := by
    rw [Nat.sub_mul]; omega
  rw [e, Nat.sub_mul_div]

theorem recip_lt (U : Nat) (h1 : 2 ^ 63 ≤ U) : (2 ^ 128 - 1) / U - 2 ^ 64 < 2 ^ 64 := by
  have : (2 ^ 128 - 1) / U < 2 ^ 65 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have := Nat.mul_le_mul_left (2 ^ 65) h1
    omega
  omega

theorem recipWord_lt (y : Nat) (hy : y ≠ 0) (h : y < 2 ^ 64) : FvModexp.AsmDiv.recipWord y < 2 ^ 64 := by
  have hn := FvModexp.AsmDiv.clz_norm64 y hy h
  unfold FvModexp.AsmDiv.recipWord
  exact recip_lt _ hn.2.1

end FvModexp.AsmDivVW
