import FvModexp.Proofs.Common.ExpBase
import Janus.Arm64.Bits

set_option autoImplicit false

/-!
# `nat.trailingZeroBits` word by word (nat.go:364-374) and `RBIT; CLZ` (agent infra)

`tz_words`: when the words `0 .. i-1` of `x` are zero and word `i` is `w ≠ 0`, `tz x = 64 i + tz w` (the loop of
`trailingZeroBits`); `ctz_rbit`: `CLZ(RBIT w) = tz w` for a non-zero 64-bit `w` (`bits.TrailingZeros64`).
-/

namespace FvModexp.Exp

theorem tz_odd {x : Nat} (h : x % 2 = 1) : tz x = 0 := by
  conv => lhs; rw [tz]
  simp [show x ≠ 0 by omega, h]

theorem tz_even {x : Nat} (hx : x ≠ 0) (h : x % 2 = 0) : tz x = 1 + tz (x / 2) := by
  conv => lhs; rw [tz]
  simp [hx, h]

theorem tz_two_mul {y : Nat} (hy : y ≠ 0) : tz (2 * y) = 1 + tz y := by
  rw [tz_even (by omega) (by omega), show 2 * y / 2 = y by omega]

theorem tz_pow_mul (k : Nat) {y : Nat} (hy : y ≠ 0) : tz (2 ^ k * y) = k + tz y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc,
      tz_two_mul (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos k)) hy), ih]; omega

theorem mod_two_pow_succ_mod2 (y k : Nat) : y % 2 ^ (k + 1) % 2 = y % 2 := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]; omega

theorem tz_mod (k : Nat) : ∀ {y : Nat}, y % 2 ^ k ≠ 0 → tz y = tz (y % 2 ^ k) := by
  induction k with
  | zero => intro y h; simp [Nat.mod_one] at h
  | succ k ih =>
    intro y h
    have hy : y ≠ 0 := by rintro rfl; simp at h
    have hm2 := mod_two_pow_succ_mod2 y k
    by_cases ho : y % 2 = 1
    · rw [tz_odd ho, tz_odd (by omega)]
    · have e : y % 2 ^ (k + 1) / 2 = y / 2 % 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]; omega
      have hk : y / 2 % 2 ^ k ≠ 0 := by
        intro h0; apply h; rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, h0]; omega
      rw [tz_even hy (by omega), tz_even h (by omega), e, ih hk]

/-- the low `i` words zero ⇒ `x % B^i = 0` -/
theorem mod_B_pow_zero (x : Nat) : ∀ i, (∀ j, j < i → wd x j = 0) → x % B ^ i = 0
  | 0, _ => by simp [Nat.mod_one]
  | i + 1, h => by
    rw [Nat.pow_succ, Nat.mod_mul, mod_B_pow_zero x i (fun j hj => h j (by omega))]
    have := h i (by omega); simp only [wd] at this; rw [this]; simp

/-- **`trailingZeroBits` from the first non-zero word** -/
theorem tz_words {x i : Nat} (hz : ∀ j, j < i → wd x j = 0) (hw : wd x i ≠ 0) : tz x = 64 * i + tz (wd x i) := by
  have hm := mod_B_pow_zero x i hz
  have hx : x = 2 ^ (64 * i) * (x / B ^ i) := by
    have := Nat.div_add_mod x (B ^ i); rw [hm, B_def, ← Nat.pow_mul, Nat.mul_comm 64 i] at this
    rw [B_def, ← Nat.pow_mul, Nat.mul_comm 64 i]; omega
  have hq : x / B ^ i ≠ 0 := by intro h0; apply hw; simp only [wd, h0, Nat.zero_mod]
  rw [show tz x = tz (2 ^ (64 * i) * (x / B ^ i)) from congrArg tz hx, tz_pow_mul _ hq,
    tz_mod 64 (by simpa [wd, B_def] using hw)]
  simp only [wd, B_def]

theorem rbitNat_lt : ∀ n x, Janus.Arm64.rbitNat n x < 2 ^ n
  | 0, _ => by simp [Janus.Arm64.rbitNat]
  | n + 1, x => by
    simp only [Janus.Arm64.rbitNat]
    have := rbitNat_lt n (x / 2)
    have : x % 2 ≤ 1 := by omega
    rw [Nat.pow_succ]
    have : x % 2 * 2 ^ n ≤ 2 ^ n := by
      calc x % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ ‹_›
        _ = 2 ^ n := Nat.one_mul _
    omega

theorem clzNat_of_lt : ∀ n v, v < 2 ^ n → ∀ m, Janus.Arm64.clzNat (n + m) v = m + Janus.Arm64.clzNat n v
  | n, v, hv, 0 => by simp
  | n, v, hv, m + 1 => by
    rw [show n + (m + 1) = (n + m) + 1 by omega, Janus.Arm64.clzNat]
    have : v.testBit (n + m) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [this, clzNat_of_lt n v hv m]; simp; omega

/-- `CLZ_n(RBIT_n x) = tz x` when the low `n` bits of `x` are not all zero -/
theorem clz_rbit : ∀ n x, x % 2 ^ n ≠ 0 → Janus.Arm64.clzNat n (Janus.Arm64.rbitNat n x) = tz x
  | 0, x, h => by simp [Nat.mod_one] at h
  | n + 1, x, h => by
    have hx : x ≠ 0 := by rintro rfl; simp at h
    have hr := rbitNat_lt n (x / 2)
    have e : Janus.Arm64.rbitNat (n + 1) x = x % 2 * 2 ^ n + Janus.Arm64.rbitNat n (x / 2) := rfl
    rw [Janus.Arm64.clzNat]
    by_cases ho : x % 2 = 1
    · have hb : (Janus.Arm64.rbitNat (n + 1) x).testBit n = true := by
        rw [e, ho, Nat.one_mul, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]; rfl
      simp only [hb, ite_true]; rw [tz_odd ho]
    · have h0 : x % 2 = 0 := by omega
      have hb : (Janus.Arm64.rbitNat (n + 1) x).testBit n = false := by
        rw [e, h0, Nat.zero_mul, Nat.zero_add]; exact Nat.testBit_lt_two_pow hr
      have hk : x / 2 % 2 ^ n ≠ 0 := by
        intro hz; apply h; rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, hz]; omega
      have e2 : Janus.Arm64.rbitNat (n + 1) x = Janus.Arm64.rbitNat n (x / 2) := by rw [e, h0]; simp
      simp only [hb, Bool.false_eq_true, ite_false]
      rw [e2, clz_rbit n (x / 2) hk, tz_even hx h0]

/-- `RBIT; CLZ` of a non-zero word (as the executor states it) -/
theorem ctz_rbit {w : Nat} (hw : w ≠ 0) (hw64 : w < 2 ^ 64) :
    Janus.Arm64.clzNat 64 (Janus.Arm64.rbitNat 64 w % 18446744073709551616) = tz w := by
  rw [Nat.mod_eq_of_lt (show Janus.Arm64.rbitNat 64 w < 18446744073709551616 from rbitNat_lt 64 w)]
  exact clz_rbit 64 w (by rw [Nat.mod_eq_of_lt hw64]; exact hw)

end FvModexp.Exp
