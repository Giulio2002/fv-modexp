import FvModexp.Proofs.Common.MulCostB

set_option autoImplicit false

/-!
# Crude uniform bounds of the `nat.mul` budget `MC` up to `258 × 129` words (ISA independent; divmc s33)

For the closed `(*Int).exp` budget (`Run.Closed.BudOK`): every multiplication there has operands of at most 258 words,
the shorter one at most 129, at stack length `ℓ ≤ 2^14`. `MC` is well-founded recursive; the bounds are by induction on
`m + n` in three layers (karatsuba halves the length: `kh 258 = 129`, `kh 129 = 65`, `kh 65 = 33 < 40`):
* `MC_box1`: `m, n ≤ N ≤ 65` — `MC ℓ m n ≤ U1 · (1 + (N - 39))` while `ℓ + 136 · (N - 39) ≤ 45056`;
* `KC_le2`: `karatsuba(n)`, `40 ≤ n ≤ 129`, `ℓ ≤ 40960` (inner products in box 1);
* `MC_box2`: `m, n ≤ N ≤ 129` — `MC ℓ m n ≤ U2 · (1 + (N - 39))` while `ℓ + 264 · (N - 39) ≤ 40960`;
* `MC_rect3`: `m ≤ 258`, `n ≤ 129`, `ℓ ≤ 16384` — `MC ℓ m n ≤ 1.3 · 10^11` (chunk loop `(m-1)/n ≤ 6` times box 2).
The box index `N - 39` bounds the chunk-loop nesting `(m, n) → (n, n)`: the chunk `(n, n)` lies in box `n ≤ N - 1`, and
`q · (n - 38) + 1 ≤ N - 38` for `q = (m - 1) / n ≥ 1`; the stack length grows by `rnd (2n) ≤ 136` (resp. `264`) per level.
-/

namespace FvModexp

/-- the chunk-loop arithmetic: `q = (m-1)/n` copies of a box-`n` bound fit in box `N` with one step to spare -/
theorem chunk_q {m n N : Nat} (h40 : 40 ≤ n) (hnm : n < m) (hmN : m ≤ N) :
    1 ≤ (m - 1) / n ∧ (m - 1) / n * (n - 38) + 1 ≤ N - 38 := by
  have h1 : 1 ≤ (m - 1) / n := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h2 := Nat.div_mul_le_self (m - 1) n
  have e3 : (m - 1) / n * (n - 38) + (m - 1) / n * 38 = (m - 1) / n * n := by
    rw [← Nat.mul_add]; congr 1; omega
  exact ⟨h1, by omega⟩

theorem MC_zero (ℓ : Nat) : MC ℓ 0 0 = 0 := by
  rw [MC_eq]; simp only [ite_true]; omega

/-- **box 1**: `m, n ≤ N ≤ 65` -/
theorem MC_box1 : ∀ (k ℓ m n N : Nat), m + n ≤ k → m ≤ N → n ≤ N → N ≤ 65 → ℓ + 136 * (N - 39) ≤ 45056 →
    MC ℓ m n ≤ 2900560 + 2900560 * (N - 39) := by
  intro k
  induction k with
  | zero =>
    intro ℓ m n N hk _ _ _ _
    rw [show m = 0 by omega, show n = 0 by omega, MC_zero]; omega
  | succ k ih =>
    intro ℓ m n N hk hm hn hN hl
    rw [MC_eq]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ 2900560 + 2900560 * (N - 39) := by
      split
      · omega
      · exact ih ℓ (m - 1) n N (by omega) (by omega) hn hN hl
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ 2900560 + 2900560 * (N - 39) := by
      split
      · omega
      · exact ih ℓ m (n - 1) N (by omega) hm (by omega) hN hl
    have hB : makeB (m + n) ≤ 2168 := by unfold makeB allocCost; omega
    have hB1 : makeB (m + 1) ≤ 2168 := by unfold makeB allocCost; omega
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        2900560 + 2900560 * (N - 39) := by
      split
      · omega
      split
      · omega
      by_cases hs : n < 40 ∨ m < n
      · rw [if_pos hs]; omega
      rw [if_neg hs]
      have hK := KC_le (ℓ := ℓ) (n := n) (by omega)
      have hS : stackNatCost ℓ (2 * n) ≤ 32 * ℓ + 4344 := by unfold stackNatCost allocCost; omega
      by_cases hlt : n < m
      · rw [if_pos hlt]
        obtain ⟨hq1, hq2⟩ := chunk_q (by omega) hlt hm
        have hI := ih (ℓ + rnd (2 * n)) n n n (by omega) (Nat.le_refl _) (Nat.le_refl _) (by omega)
          (by simp only [rnd]; omega)
        have hQ := Nat.mul_le_mul_left ((m - 1) / n) hI
        have e1 : (m - 1) / n * (2900560 + 2900560 * (n - 39)) = 2900560 * ((m - 1) / n * (n - 38)) := by
          rw [show 2900560 + 2900560 * (n - 39) = 2900560 * (n - 38) by omega, Nat.mul_left_comm]
        omega
      · rw [if_neg hlt]; omega
    omega

/-- `karatsuba(n)` for `40 ≤ n ≤ 129` (inner products: box 1) -/
theorem KC_le2 {ℓ n : Nat} (hn : n ≤ 129) (hl : ℓ ≤ 40960) : KC ℓ n ≤ 236269256 := by
  have hk : kh n ≤ 65 := by simp only [kh]; omega
  have e1 : stackNatCost ℓ (2 * kh n + 1) ≤ 1315096 := by unfold stackNatCost allocCost; omega
  have e2 : asB (2 * kh n + 1) ≤ 2200 := by unfold asB allocCost; omega
  have e3 := MC_box1 (kh n + kh n) (ℓ + rnd (2 * kh n + 1)) (kh n) (kh n) 65 (Nat.le_refl _) hk hk (Nat.le_refl _)
    (by simp only [rnd]; omega)
  unfold KC; omega

/-- **box 2**: `m, n ≤ N ≤ 129` -/
theorem MC_box2 : ∀ (k ℓ m n N : Nat), m + n ≤ k → m ≤ N → n ≤ N → N ≤ 129 → ℓ + 264 * (N - 39) ≤ 40960 →
    MC ℓ m n ≤ 237592632 + 237592632 * (N - 39) := by
  intro k
  induction k with
  | zero =>
    intro ℓ m n N hk _ _ _ _
    rw [show m = 0 by omega, show n = 0 by omega, MC_zero]; omega
  | succ k ih =>
    intro ℓ m n N hk hm hn hN hl
    rw [MC_eq]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ 237592632 + 237592632 * (N - 39) := by
      split
      · omega
      · exact ih ℓ (m - 1) n N (by omega) (by omega) hn hN hl
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ 237592632 + 237592632 * (N - 39) := by
      split
      · omega
      · exact ih ℓ m (n - 1) N (by omega) hm (by omega) hN hl
    have hB : makeB (m + n) ≤ 4216 := by unfold makeB allocCost; omega
    have hB1 : makeB (m + 1) ≤ 4216 := by unfold makeB allocCost; omega
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        237592632 + 237592632 * (N - 39) := by
      split
      · omega
      split
      · omega
      by_cases hs : n < 40 ∨ m < n
      · rw [if_pos hs]; omega
      rw [if_neg hs]
      have hK := KC_le2 (ℓ := ℓ) (n := n) (by omega) (by omega)
      have hS : stackNatCost ℓ (2 * n) ≤ 1319160 := by unfold stackNatCost allocCost; omega
      by_cases hlt : n < m
      · rw [if_pos hlt]
        obtain ⟨hq1, hq2⟩ := chunk_q (by omega) hlt hm
        have hI := ih (ℓ + rnd (2 * n)) n n n (by omega) (Nat.le_refl _) (Nat.le_refl _) (by omega)
          (by simp only [rnd]; omega)
        have hQ := Nat.mul_le_mul_left ((m - 1) / n) hI
        have e1 : (m - 1) / n * (237592632 + 237592632 * (n - 39)) =
            237592632 * ((m - 1) / n * (n - 38)) := by
          rw [show 237592632 + 237592632 * (n - 39) = 237592632 * (n - 38) by omega, Nat.mul_left_comm]
        omega
      · rw [if_neg hlt]; omega
    omega

/-- **rectangle 3**: `m ≤ 258`, `n ≤ 129`, `ℓ ≤ 2^14` (one chunk-loop level of at most 6 box-2 products) -/
theorem MC_rect3 : ∀ (k ℓ m n : Nat), m + n ≤ k → m ≤ 258 → n ≤ 129 → ℓ ≤ 16384 → MC ℓ m n ≤ 130000000000 := by
  intro k
  induction k with
  | zero =>
    intro ℓ m n hk _ _ _
    rw [show m = 0 by omega, show n = 0 by omega, MC_zero]; omega
  | succ k ih =>
    intro ℓ m n hk hm hn hl
    rw [MC_eq]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ 130000000000 := by
      split
      · omega
      · exact ih ℓ (m - 1) n (by omega) (by omega) hn hl
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ 130000000000 := by
      split
      · omega
      · exact ih ℓ m (n - 1) (by omega) hm (by omega) hl
    have hB : makeB (m + n) ≤ 6280 := by unfold makeB allocCost; omega
    have hB1 : makeB (m + 1) ≤ 6280 := by unfold makeB allocCost; omega
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        130000000000 := by
      split
      · omega
      split
      · omega
      by_cases hs : n < 40 ∨ m < n
      · rw [if_pos hs]; omega
      rw [if_neg hs]
      have hK := KC_le2 (ℓ := ℓ) (n := n) hn (by omega)
      have hS : stackNatCost ℓ (2 * n) ≤ 532728 := by unfold stackNatCost allocCost; omega
      by_cases hlt : n < m
      · rw [if_pos hlt]
        have hq : (m - 1) / n ≤ 6 :=
          Nat.le_trans (Nat.div_le_div_left (c := 40) (by omega) (by omega)) (by omega)
        have hI := MC_box2 (n + n) (ℓ + rnd (2 * n)) n n 129 (Nat.le_refl _) hn hn (Nat.le_refl _)
          (by simp only [rnd]; omega)
        have hQ := Nat.mul_le_mul hq hI
        omega
      · rw [if_neg hlt]; omega
    omega

/-- `z.mul(stk, x, y)` with `x, y ≤ 129` words at stack length `ℓ ≤ 2^14` -/
theorem mulC_le2 {ℓ x y : Nat} (hl : ℓ ≤ 16384) (hx : x ≤ 129) (hy : y ≤ 129) : mulC ℓ x y ≤ 21620929512 := by
  have := MC_box2 (max x y + min x y) ℓ (max x y) (min x y) 129 (Nat.le_refl _) (by omega) (by omega)
    (Nat.le_refl _) (by omega)
  unfold mulC; omega

/-- `z.mul(stk, x, y)` with at most `258` words, the shorter at most `129`, at stack length `ℓ ≤ 2^14` -/
theorem mulC_le3 {ℓ x y : Nat} (hl : ℓ ≤ 16384) (hx : max x y ≤ 258) (hy : min x y ≤ 129) :
    mulC ℓ x y ≤ 130000000000 :=
  MC_rect3 (max x y + min x y) ℓ (max x y) (min x y) (Nat.le_refl _) hx hy hl

/-- `z.sqr(stk, x)` with `x ≤ 129` words at stack length `ℓ ≤ 2^14` (one karatsuba level: `(n+1)/2 ≤ 65 < 80`) -/
theorem sqrC_le {ℓ n : Nat} (hl : ℓ ≤ 16384) (hn : n ≤ 129) : sqrC ℓ n ≤ 2700000 := by
  have hB : makeB (2 * n) ≤ 4216 := by unfold makeB allocCost; omega
  have hK : ksqrC ℓ n ≤ 2673064 := by
    by_cases h80 : 80 ≤ n
    · rw [ksqrC_big h80, ksqrC_small (by omega)]
      have hB2 : makeB (2 * ((n + 1) / 2)) ≤ 2168 := by unfold makeB allocCost; omega
      unfold stackNatCost asB allocCost; omega
    · rw [ksqrC_small (by omega)]; unfold stackNatCost allocCost; omega
  unfold sqrC; split <;> omega

end FvModexp
