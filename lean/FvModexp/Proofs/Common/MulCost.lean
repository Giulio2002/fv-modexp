import FvModexp.Proofs.Common.SqrCost

/-!
# Budgets and stack windows of the multiplication SCC `{nat.mul, karatsuba, (*Int).mul}` (ISA independent; divmc)

go-bigmodexpfix natmul.go:16 (`nat.mul`), :164 (`karatsuba`), int.go:191 (`(*Int).mul`).

## Budget (`MC ℓ m n`, `m ≥ n` the operand lengths after the swap, `ℓ` the stack length at entry)
`nat.mul(m ≥ n)`: `n = 0` nothing; `n = 1` `z.mulAddWW` (`make(m + 1)`); else `z.make(m + n)`, then for `n ≥ 40`
`karatsuba(n)` (`KC ℓ n`: `stk.nat(2·n2 + 1)`, four `(*Int).Add/Sub`, three `(*Int).mul` on operands of `≤ n2` words at
the stack length `ℓ + rnd (2·n2 + 1)`) and for `n < m` the chunk loop: `stk.nat(2n)` and `(m - 1) / n` calls
`t.mul(x[i:i+c], y)` (`c ≤ n`) at the stack length `ℓ + rnd (2n)`.
`MC` is MONOTONE BY CONSTRUCTION in both lengths (`max` with the two smaller instances), so a call on operands shorter
than the nominal ones (normalised halves, the last chunk) stays within the allowance; it is monotone in `ℓ`
(`MC_mono`). The exported cost is `mulC ℓ xl yl = MC ℓ (max xl yl) (min xl yl)` (symmetric: the swap is free).

## Stack windows (arm64 frames: `nat.mul` 256 + 88 above, `karatsuba` 448 + 72, `(*Int).mul` 96 + 40)
`mulW m n = 1056·log₂(m·n) + 4608 (+ 256 if m < n)`: the chunk loop's inner `t.mul(c, n)` has `2·c·n ≤ m·n` (one
`log₂` step pays the loop frame and the swap frame), `karatsuba(n)`'s inner products have `2·n2² ≤ m·n` (one step pays
the `nat.mul`, `karatsuba` and `(*Int).mul` frames). The depth is logarithmic: `mulW xl yl ≤ mulWX = 30208` for
`xl, yl ≤ 2^12` (`mulW_le_X`).
-/

namespace FvModexp

/-- `n2 = (n + 1) / 2` -/
abbrev kh (n : Nat) : Nat := (n + 1) / 2

/-- the stack length after `stk.nat(k)` -/
abbrev rnd (k : Nat) : Nat := (k + 3) / 4 * 4

/-- **the budget of `nat.mul` with operands of `m ≥ n` words at stack length `ℓ`** (see the module doc) -/
def MC (ℓ m n : Nat) : Nat :=
  max (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if h : n < 40 ∨ m < n then 0 else
          (stackNatCost ℓ (2 * kh n + 1) + 4 * asB (2 * kh n + 1) +
            3 * MC (ℓ + rnd (2 * kh n + 1)) (kh n) (kh n)) +
          if h' : n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0)
    (max (if hm : m = 0 then 0 else MC ℓ (m - 1) n) (if hn : n = 0 then 0 else MC ℓ m (n - 1)))
termination_by m + n
decreasing_by all_goals (try simp only [kh]); all_goals omega

/-- `karatsuba(n)` at stack length `ℓ` -/
def KC (ℓ n : Nat) : Nat :=
  stackNatCost ℓ (2 * kh n + 1) + 4 * asB (2 * kh n + 1) + 3 * MC (ℓ + rnd (2 * kh n + 1)) (kh n) (kh n)

/-- the exported cost of `z.mul(stk, x, y)` (`len x = xl`, `len y = yl`, stack length `ℓ`) -/
def mulC (ℓ xl yl : Nat) : Nat := MC ℓ (max xl yl) (min xl yl)

theorem mulC_comm (ℓ xl yl : Nat) : mulC ℓ xl yl = mulC ℓ yl xl := by
  unfold mulC; rw [Nat.max_comm, Nat.min_comm]

theorem MC_eq (ℓ m n : Nat) : MC ℓ m n =
    max (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0)
    (max (if m = 0 then 0 else MC ℓ (m - 1) n) (if n = 0 then 0 else MC ℓ m (n - 1))) := by
  rw [MC]; simp only [dite_eq_ite, KC]

theorem MC_left (ℓ m n : Nat) : MC ℓ m n ≤ MC ℓ (m + 1) n := by
  rw [MC_eq ℓ (m + 1) n]; simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]; omega

theorem MC_right (ℓ m n : Nat) : MC ℓ m n ≤ MC ℓ m (n + 1) := by
  rw [MC_eq ℓ m (n + 1)]; simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]; omega

/-- monotone in both lengths -/
theorem MC_len {ℓ m n m' n' : Nat} (hm : m ≤ m') (hn : n ≤ n') : MC ℓ m n ≤ MC ℓ m' n' := by
  have h1 : ∀ k, MC ℓ m n ≤ MC ℓ (m + k) n := by
    intro k; induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (MC_left ℓ (m + k) n)
  have h2 : ∀ k, MC ℓ m' n ≤ MC ℓ m' (n + k) := by
    intro k; induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (MC_right ℓ m' (n + k))
  have := h1 (m' - m); have := h2 (n' - n)
  rw [show m + (m' - m) = m' by omega] at *; rw [show n + (n' - n) = n' by omega] at *; omega

theorem stackNatCost_ell {ℓ ℓ' n : Nat} (h : ℓ ≤ ℓ') : stackNatCost ℓ n ≤ stackNatCost ℓ' n :=
  stackNatCost_mono h (Nat.le_refl n)

/-- monotone in the stack length -/
theorem MC_mono : ∀ (k ℓ ℓ' m n : Nat), m + n ≤ k → ℓ ≤ ℓ' → MC ℓ m n ≤ MC ℓ' m n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro ℓ ℓ' m n hk hl
    rw [MC_eq ℓ m n, MC_eq ℓ' m n]
    have a1 : (if m = 0 then 0 else MC ℓ (m - 1) n) ≤ (if m = 0 then 0 else MC ℓ' (m - 1) n) := by
      split
      · exact Nat.le_refl _
      · exact ih (m - 1 + n) (by omega) ℓ ℓ' (m - 1) n (Nat.le_refl _) hl
    have a2 : (if n = 0 then 0 else MC ℓ m (n - 1)) ≤ (if n = 0 then 0 else MC ℓ' m (n - 1)) := by
      split
      · exact Nat.le_refl _
      · exact ih (m + (n - 1)) (by omega) ℓ ℓ' m (n - 1) (Nat.le_refl _) hl
    have a3 : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ n + if n < m then stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n else 0) ≤
        (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KC ℓ' n + if n < m then stackNatCost ℓ' (2 * n) + (m - 1) / n * MC (ℓ' + rnd (2 * n)) n n else 0) := by
      split
      · exact Nat.le_refl _
      split
      · exact Nat.le_refl _
      split
      · exact Nat.le_refl _
      rename_i h0 h1 h40
      have hkh : kh n = (n + 1) / 2 := rfl
      have hk1 : KC ℓ n ≤ KC ℓ' n := by
        unfold KC
        have := stackNatCost_ell (n := 2 * kh n + 1) hl
        have := ih (kh n + kh n) (by omega) (ℓ + rnd (2 * kh n + 1)) (ℓ' + rnd (2 * kh n + 1)) (kh n) (kh n)
          (Nat.le_refl _) (by omega)
        omega
      split
      · have := stackNatCost_ell (n := 2 * n) hl
        have := ih (n + n) (by omega) (ℓ + rnd (2 * n)) (ℓ' + rnd (2 * n)) n n (Nat.le_refl _) (by omega)
        have := Nat.mul_le_mul_left ((m - 1) / n) this
        omega
      · omega
    omega

theorem mulC_mono {ℓ ℓ' xl xl' yl yl' : Nat} (h1 : ℓ ≤ ℓ') (h2 : xl ≤ xl') (h3 : yl ≤ yl') :
    mulC ℓ xl yl ≤ mulC ℓ' xl' yl' := by
  unfold mulC
  exact Nat.le_trans (MC_len (by omega) (by omega)) (MC_mono _ ℓ ℓ' _ _ (Nat.le_refl _) h1)

/-! ## The paths of `nat.mul(m ≥ n)` -/

theorem MC_one {ℓ m : Nat} : makeB (m + 1) ≤ MC ℓ m 1 := by
  rw [MC_eq ℓ m 1]; simp only [Nat.one_ne_zero, ite_false, ite_true]; omega

theorem MC_basic {ℓ m n : Nat} (h2 : 2 ≤ n) : makeB (m + n) ≤ MC ℓ m n := by
  rw [MC_eq ℓ m n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega)]; omega

/-- `karatsuba(n)` with `m = n` -/
theorem MC_kar {ℓ n : Nat} (h40 : 40 ≤ n) : makeB (n + n) + KC ℓ n ≤ MC ℓ n n := by
  rw [MC_eq ℓ n n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega),
    if_neg (show ¬ (n < 40 ∨ n < n) by omega), if_neg (show ¬ n < n by omega)]; omega

/-- `karatsuba(n)` and the chunk loop (`n < m`) -/
theorem MC_loop {ℓ m n : Nat} (h40 : 40 ≤ n) (hm : n < m) :
    makeB (m + n) + KC ℓ n + (stackNatCost ℓ (2 * n) + (m - 1) / n * MC (ℓ + rnd (2 * n)) n n) ≤ MC ℓ m n := by
  rw [MC_eq ℓ m n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega),
    if_neg (show ¬ (n < 40 ∨ m < n) by omega), if_pos hm]; omega

/-- an inner product of `karatsuba(n)` (operands `≤ n2` words) at the inner stack length -/
theorem mulC_le_inner {ℓ n a b : Nat} (ha : a ≤ kh n) (hb : b ≤ kh n) : mulC ℓ a b ≤ MC ℓ (kh n) (kh n) := by
  unfold mulC; exact MC_len (by omega) (by omega)

/-- a chunk product `t.mul(x[i:i+c], y)` (`c ≤ n`) -/
theorem mulC_le_chunk {ℓ n c : Nat} (hc : c ≤ n) : mulC ℓ c n ≤ MC ℓ n n := by
  unfold mulC; exact MC_len (by omega) (by omega)

/-! ## Stack windows -/

/-- the window of `nat.mul` (`len x = m`, `len y = n`) at its entry -/
def mulW (m n : Nat) : Nat := 1056 * Nat.log2 (m * n) + 4608 + if m < n then 256 else 0

/-- the window of `karatsuba` on `n`-word operands -/
def kW (n : Nat) : Nat := 1056 * Nat.log2 (kh n * kh n) + 4608 + 800

/-- the window of `(*Int).mul` on operands of `xl`, `yl` words -/
def imW (xl yl : Nat) : Nat := mulW xl yl + 96

/-- the exported window (`xl, yl ≤ 2^12`) -/
abbrev mulWX : Nat := 30208

theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Nat.log2_zero]
  exact (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (by omega)) h)

theorem log2_step {a b : Nat} (ha : 0 < a) (h : 2 * a ≤ b) : Nat.log2 a + 1 ≤ Nat.log2 b := by
  refine (Nat.le_log2 (by omega)).2 ?_
  have := Nat.log2_self_le (n := a) (by omega)
  rw [Nat.pow_succ]; omega

theorem mulW_ge (m n : Nat) : 4608 ≤ mulW m n := by unfold mulW; omega

theorem kW_ge (n : Nat) : 5408 ≤ kW n := by unfold kW; omega

theorem mulW_swap {m n : Nat} (h : m < n) : mulW n m + 256 ≤ mulW m n := by
  unfold mulW; rw [Nat.mul_comm n m, if_neg (by omega), if_pos h]; omega

/-- the chunk product `t.mul(c, n)` (`0 < c ≤ n`, `2c ≤ m`) one `nat.mul` frame down -/
theorem mulW_chunk {m n c : Nat} (hc0 : 0 < c) (hcn : c ≤ n) (h2 : 2 * c ≤ m) : mulW c n + 256 ≤ mulW m n := by
  have hp : 0 < c * n := Nat.mul_pos hc0 (by omega)
  have : 2 * (c * n) ≤ m * n := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right n h2
  have := log2_step hp this
  unfold mulW; split <;> split <;> omega

theorem two_kh_sq {n : Nat} (h : 40 ≤ n) : 2 * (kh n * kh n) ≤ n * n := by
  have hkh : kh n = (n + 1) / 2 := rfl
  have h1 : 2 * kh n ≤ n + 1 := by omega
  have h2 : (2 * kh n) * (2 * kh n) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul h1 h1
  have h3 : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have h4 : 40 * n ≤ n * n := Nat.mul_le_mul_right n h
  have h5 : (2 * kh n) * (2 * kh n) = 4 * (kh n * kh n) := by
    rw [Nat.mul_assoc, Nat.mul_comm (kh n) (2 * kh n), Nat.mul_assoc, ← Nat.mul_assoc]
  omega

/-- `karatsuba(n)` (`40 ≤ n ≤ m`) one `nat.mul` frame down -/
theorem kW_call {m n : Nat} (h40 : 40 ≤ n) (hnm : n ≤ m) : kW n + 256 ≤ mulW m n := by
  have hkh : kh n = (n + 1) / 2 := rfl
  have hp : 0 < kh n * kh n := Nat.mul_pos (by omega) (by omega)
  have h1 := two_kh_sq h40
  have h2 : n * n ≤ m * n := Nat.mul_le_mul_right n hnm
  have := log2_step hp (Nat.le_trans h1 h2)
  unfold kW mulW; rw [if_neg (by omega)]; omega

/-- an inner `(*Int).mul` of `karatsuba(n)` (operands `≤ n2` words) one `karatsuba` frame down -/
theorem imW_inner {n a b : Nat} (ha : a ≤ kh n) (hb : b ≤ kh n) : imW a b + 448 ≤ kW n := by
  have := log2_mono (Nat.mul_le_mul ha hb)
  unfold imW mulW kW; split <;> omega

/-- `nat.mul` one `(*Int).mul` frame down -/
theorem imW_call (a b : Nat) : mulW a b + 96 ≤ imW a b := Nat.le_refl _

theorem mulW_le_X {xl yl : Nat} (hx : xl ≤ 2 ^ 12) (hy : yl ≤ 2 ^ 12) : mulW xl yl ≤ mulWX := by
  have h1 : xl * yl ≤ 2 ^ 12 * 2 ^ 12 := Nat.mul_le_mul hx hy
  have h2 : Nat.log2 (xl * yl) ≤ 24 := by
    have := log2_mono h1
    rw [show (2 : Nat) ^ 12 * 2 ^ 12 = 2 ^ 24 from rfl, Nat.log2_two_pow] at this; exact this
  unfold mulW mulWX; split <;> omega

end FvModexp
