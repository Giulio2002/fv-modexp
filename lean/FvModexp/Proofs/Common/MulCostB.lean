import FvModexp.Proofs.Common.MulCost

set_option autoImplicit false

/-!
# Numeric upper bounds of the `nat.mul` budget `MC` for operands of at most 65 words (ISA independent; divmc)

Used by the `(*Int).Mod` budget lemma (`nat.div`'s `divRecursiveStep` multiplies `qhat · v[:B-1]` with `B ≤ 64`).
`MC` is well-founded recursive (no evaluation by `decide`); the bounds are by induction on `m + n`:
* `MC_small`: `n < 40` (schoolbook only) — `MC ℓ m n ≤ makeB (m + n)`;
* `KC_le`: `karatsuba(n)` for `n ≤ 65` (its three inner products have `≤ 33 < 40` words) — `≤ 32 ℓ + 10464`;
* `MC_bnd`: `m, n ≤ 65` — `MC ℓ m n ≤ 133336 + J m n · 258384` as long as `ℓ + 133 · J m n ≤ 3772`, where `J m n` bounds
  the nesting depth of the chunk loop (`(m - 1) / n ≤ 1` here: one loop level `(m, n) → (n, n)` per step, `J` drops by
  one, the stack length grows by `rnd (2n) ≤ 133`).
-/

namespace FvModexp

/-- `nat.mul` without `karatsuba` (`n < 40`): every path makes at most `m + n` words -/
theorem MC_small : ∀ (k ℓ m n : Nat), m + n ≤ k → n < 40 → MC ℓ m n ≤ makeB (m + n) := by
  intro k
  induction k with
  | zero =>
    intro ℓ m n hk _
    rw [MC_eq]; simp only [show m = 0 by omega, show n = 0 by omega, ite_true]; omega
  | succ k ih =>
    intro ℓ m n hk hn
    rw [MC_eq]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ makeB (m + n) := by
      split
      · omega
      · exact Nat.le_trans (ih ℓ (m - 1) n (by omega) hn) (makeB_mono (by omega))
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ makeB (m + n) := by
      split
      · omega
      · exact Nat.le_trans (ih ℓ m (n - 1) (by omega) (by omega)) (makeB_mono (by omega))
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        makeB (m + n) := by
      split
      · omega
      split
      · subst_vars; exact Nat.le_refl _
      rw [if_pos (Or.inl hn)]; omega
    omega

/-- `karatsuba(n)` for `n ≤ 65` -/
theorem KC_le {ℓ n : Nat} (hn : n ≤ 65) : KC ℓ n ≤ 32 * ℓ + 10464 := by
  have hk : kh n ≤ 33 := by simp only [kh]; omega
  have e1 : stackNatCost ℓ (2 * kh n + 1) ≤ 32 * ℓ + 2328 := by unfold stackNatCost allocCost; omega
  have e2 : asB (2 * kh n + 1) ≤ 1176 := by unfold asB allocCost; omega
  have e3 : MC (ℓ + rnd (2 * kh n + 1)) (kh n) (kh n) ≤ 1144 :=
    Nat.le_trans (MC_small (kh n + kh n) _ (kh n) (kh n) (Nat.le_refl _) (by omega))
      (by unfold makeB allocCost; omega)
  unfold KC; omega

/-- the chunk-loop depth bound -/
def mulJ (m n : Nat) : Nat := if n < m then (m + n - 79) / 2 else (m + n - 80) / 2

theorem mulJ_lt {m n : Nat} (h : n < m) : mulJ m n = (m + n - 79) / 2 := if_pos h
theorem mulJ_ge {m n : Nat} (h : ¬ n < m) : mulJ m n = (m + n - 80) / 2 := if_neg h

theorem mulJ_l {m n : Nat} (h : 0 < m) : mulJ (m - 1) n ≤ mulJ m n := by
  by_cases h1 : n < m - 1
  · rw [mulJ_lt h1, mulJ_lt (by omega)]; omega
  · rw [mulJ_ge h1]; by_cases h2 : n < m
    · rw [mulJ_lt h2]; omega
    · rw [mulJ_ge h2]; omega

theorem mulJ_r {m n : Nat} (h : 0 < n) : mulJ m (n - 1) ≤ mulJ m n := by
  by_cases h1 : n - 1 < m
  · rw [mulJ_lt h1]; by_cases h2 : n < m
    · rw [mulJ_lt h2]; omega
    · rw [mulJ_ge h2]; omega
  · rw [mulJ_ge h1, mulJ_ge (by omega)]; omega

/-- **`nat.mul` on operands of at most 65 words** -/
theorem MC_bnd : ∀ (k ℓ m n : Nat), m + n ≤ k → m ≤ 65 → n ≤ 65 → ℓ + 133 * mulJ m n ≤ 3772 →
    MC ℓ m n ≤ 133336 + 258384 * mulJ m n := by
  intro k
  induction k with
  | zero =>
    intro ℓ m n hk _ _ _
    have := MC_small 0 ℓ m n hk (by omega)
    have := makeB_mono (k := m + n) (k' := 130) (by omega)
    unfold makeB allocCost at *; omega
  | succ k ih =>
    intro ℓ m n hk hm hn hl
    by_cases h40 : n < 40
    · have := MC_small (m + n) ℓ m n (Nat.le_refl _) h40
      have := makeB_mono (k := m + n) (k' := 130) (by omega)
      unfold makeB allocCost at *; omega
    rw [MC_eq]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ 133336 + 258384 * mulJ m n := by
      split
      · omega
      · have hj := mulJ_l (m := m) (n := n) (by omega)
        have := ih ℓ (m - 1) n (by omega) (by omega) hn (by omega)
        omega
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ 133336 + 258384 * mulJ m n := by
      split
      · omega
      · have hj := mulJ_r (m := m) (n := n) (by omega)
        have := ih ℓ m (n - 1) (by omega) hm (by omega) (by omega)
        omega
    have hB := makeB_mono (k := m + n) (k' := 130) (by omega)
    have hK := KC_le (ℓ := ℓ) hn
    unfold makeB allocCost at hB
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        133336 + 258384 * mulJ m n := by
      rw [if_neg (by omega), if_neg (by omega)]
      unfold makeB allocCost
      by_cases hmn : m < n
      · rw [if_pos (Or.inr hmn)]; omega
      rw [if_neg (by omega)]
      by_cases hlt : n < m
      · rw [if_pos hlt]
        have hj := mulJ_lt hlt
        have hjn : mulJ n n = n - 40 := by rw [mulJ_ge (by omega)]; omega
        have hq : (m - 1) / n ≤ 1 := by
          have := (Nat.div_lt_iff_lt_mul (x := m - 1) (y := 2) (k := n) (by omega)).2 (by omega); omega
        have hr : rnd (2 * n) ≤ 133 := by simp only [rnd]; omega
        have hI := ih (ℓ + rnd (2 * n)) n n (by omega) hn hn (by omega)
        have hQ := Nat.mul_le_mul_right (MC (ℓ + rnd (2 * n)) n n) hq
        have hS : stackNatCost ℓ (2 * n) ≤ 32 * ℓ + 4344 := by unfold stackNatCost allocCost; omega
        omega
      · rw [if_neg hlt]
        have hj := mulJ_ge hlt
        omega
    omega

end FvModexp
