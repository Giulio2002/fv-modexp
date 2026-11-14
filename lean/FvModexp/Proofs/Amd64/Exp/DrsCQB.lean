import FvModexp.Proofs.Amd64.NatQ.DivHypQ
import FvModexp.Proofs.Common.MulCostQB

set_option autoImplicit false

/-!
# A closed linear bound of amd64 `drsCQ` (TIGHT COSTS BudOK; agent expmc s83, verbatim copy of arm64 ExpQ/DrsCQB, s44)

`Q.drsCQ U n ≤ 560·U + 88·n + 1400` for divisors `n ≤ 128` and dividends `U ≤ 385` (`3·128 + 1`: `nat.expNNSlow`'s
`3·max xl ml`-word reductions; the windows' and `nat.rem`'s divisions are shorter). From divmc's MulCostQB
(`mulCQ_le_B`, `mulCB`). Two recursion levels: `40 ≤ n ≤ 76` (the inner divisor `n - n/2 + 1 < 40`) and
`77 ≤ n ≤ 128` (inner divisor in `[40, 65]`, its inner one `< 40`). Numbers: scratchpad mirror, max `drsCQ/U = 440`.
-/

namespace FvModexp.Amd64.Q

/-- the half-size multiplication of a step, `h = n/2 ≥ 20`, `h - 1 < 40` -/
theorem mulh_le0 {h : Nat} (h0 : 1 ≤ h) (h1 : h - 1 < 40) : mulCQ (h + 1) (h - 1) ≤ 32 * h + 88 := by
  have := mulCQ_le_B (xl := h + 1) (yl := h - 1) (by omega)
  rw [show max (h + 1) (h - 1) = h + 1 by omega, show min (h + 1) (h - 1) = h - 1 by omega] at this
  unfold mulCB at this; rw [if_pos h1] at this; omega

/-- the same for `h ≤ 64` -/
theorem mulh_le1 {h : Nat} (h1 : h ≤ 64) : mulCQ (h + 1) (h - 1) ≤ 160 * h + 1192 := by
  by_cases h40 : h - 1 < 40
  · by_cases h0 : 1 ≤ h
    · have := mulh_le0 h0 h40; omega
    · have := mulCQ_le_B (xl := h + 1) (yl := h - 1) (by omega); unfold mulCB at this
      rw [if_pos (by omega)] at this; omega
  · have := mulCQ_le_box1 (xl := h + 1) (yl := h - 1) (n := h + 1) (by omega) (by omega) (by omega); omega

/-- level 1: `40 ≤ n ≤ 76` -/
theorem drsCQ_le1 {U n : Nat} (h40 : 40 ≤ n) (h76 : n ≤ 76) : drsCQ U n ≤ 37 * U + 16 * n + 88 := by
  rw [drsCQ_big (by omega), drsCQ_small (n := n - n / 2 + 1) (by omega), Nat.zero_add]
  have hm := mulh_le0 (h := n / 2) (by omega) (by omega)
  have hh : 20 ≤ n / 2 := by omega
  have hh2 : 2 * (n / 2) ≤ n := by omega
  have hk := Nat.div_mul_le_self (U - n) (n / 2)
  generalize n / 2 = h at hm hh hh2 hk ⊢
  generalize (U - n) / h = k at hk ⊢
  have hk20 : 20 * k ≤ k * h := by rw [Nat.mul_comm 20 k]; exact Nat.mul_le_mul_left k hh
  have e1 : (k + 1) * mulCQ (h + 1) (h - 1) ≤ (k + 1) * (32 * h + 88) := Nat.mul_le_mul_left _ hm
  have e2 : (k + 1) * (32 * h + 88) = 32 * (k * h) + 88 * k + 32 * h + 88 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; rw [Nat.mul_left_comm k 32 h]; omega
  omega

/-- level 2: `77 ≤ n ≤ 128`, `U ≤ 385` -/
theorem drsCQ_le2 {U n : Nat} (h77 : 77 ≤ n) (h128 : n ≤ 128) (hU : U ≤ 385) : drsCQ U n ≤ 544 * U + 88 * n + 1312 := by
  rw [drsCQ_big (by omega)]
  have hi := drsCQ_le1 (U := U) (n := n - n / 2 + 1) (by omega) (by omega)
  have hm := mulh_le1 (h := n / 2) (by omega)
  have hh : 38 ≤ n / 2 := by omega
  have hh2 : 2 * (n / 2) ≤ n := by omega
  have hn' : n - n / 2 + 1 ≤ n / 2 + 2 := by omega
  have hk := Nat.div_mul_le_self (U - n) (n / 2)
  have hk8 : (U - n) / (n / 2) ≤ 8 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]; omega
  generalize drsCQ U (n - n / 2 + 1) = d at hi ⊢
  generalize n - n / 2 + 1 = n' at hi hn'
  generalize n / 2 = h at hm hh hh2 hk hk8 hn' ⊢
  generalize (U - n) / h = k at hk hk8 ⊢
  have hk38 : 38 * k ≤ k * h := by rw [Nat.mul_comm 38 k]; exact Nat.mul_le_mul_left k hh
  have hkU : k * U ≤ 8 * U := Nat.mul_le_mul_right U hk8
  have e1 : (k + 1) * (d + mulCQ (h + 1) (h - 1)) ≤ (k + 1) * (37 * U + 176 * h + 1312) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : (k + 1) * (37 * U + 176 * h + 1312) = 37 * (k * U) + 176 * (k * h) + 1312 * k + 37 * U + 176 * h + 1312 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; rw [Nat.mul_left_comm k 37 U, Nat.mul_left_comm k 176 h]; omega
  omega

/-- **the closed bound** -/
theorem drsCQ_le {U n : Nat} (hn : n ≤ 128) (hU : U ≤ 385) : drsCQ U n ≤ 560 * U + 88 * n + 1400 := by
  by_cases h40 : n < 40
  · rw [drsCQ_small h40]; omega
  by_cases h76 : n ≤ 76
  · have := drsCQ_le1 (U := U) (n := n) (by omega) h76; omega
  · have := drsCQ_le2 (U := U) (n := n) (by omega) hn hU; omega

end FvModexp.Amd64.Q
