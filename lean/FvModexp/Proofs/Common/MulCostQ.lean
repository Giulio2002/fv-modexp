import FvModexp.Proofs.Common.MulCost
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# Level-free (Q-form) budgets of `{nat.mul, karatsuba, (*Int).mul}` and `{nat.sqr, karatsubaSqr, basicSqr}` (divmc)

TIGHT COSTS (NOTES-conventions "[divmc s34] TIGHT COSTS step 2"): with the amortised stack accounting of Common/StackPot
a `stk.nat` costs nothing (the reserve `stkR H` pays every growth), so the budgets below have NO stack-level argument
and NO stack terms. They are the consumption `C` of the Q-form summaries (pre `C + stkR H s.mem st ≤ b`).

`MCQ m n` (`m ≥ n` after the swap; go-bigmodexpfix natmul.go:16): `n = 0` nothing; `n = 1` `z.mulAddWW` (`make(m+1)`);
else `z.make(m + n)`, then for `n ≥ 40` `karatsuba(n)` (`KCQ n`: four `(*Int).Add/Sub`, three `(*Int).mul` on `≤ n2`
words) and for `n < m` the chunk loop `for i := n; i < m; i += n { t = t.mul(stk, x[i:min(i+n, m)], y) }`: chunk `k`
(0-based) has `min n (m - (k+1)·n)` words — CHARGED AT ITS REAL LENGTH (`chunkSum`; the last one is short:
`chunkSum_eq`: `((m-1)/n - 1)` full chunks + one of `(m-1) % n + 1` words). Monotone in both lengths by construction.
`sqrCQ n` (natmul.go:73/:257): `z.make(2n)`, for `n ≥ 80` `karatsubaSqr` (`Sub`, three `sqr` on `≤ n2` words, two `Add`).
-/

namespace FvModexp

/-- the chunk loop's budget: chunks `0 … k-1`, chunk `j` of `min n (m - (j+1)·n)` words, each costing `f` of its length -/
def chunkSum (f : Nat → Nat) (n m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => chunkSum f n m k + f (m - (k + 1) * n)

/-- **the level-free budget of `nat.mul` with operands of `m ≥ n` words** -/
def MCQ (m n : Nat) : Nat :=
  max (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if h : n < 40 ∨ m < n then 0 else
          (4 * asB (2 * kh n + 1) + 3 * MCQ (kh n) (kh n)) +
          if h' : n < m then chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) else 0)
    (max (if hm : m = 0 then 0 else MCQ (m - 1) n) (if hn : n = 0 then 0 else MCQ m (n - 1)))
termination_by m + n
decreasing_by all_goals (try simp only [kh]); all_goals omega

/-- `karatsuba(n)` -/
def KCQ (n : Nat) : Nat := 4 * asB (2 * kh n + 1) + 3 * MCQ (kh n) (kh n)

/-- the exported budget of `z.mul(stk, x, y)` (`len x = xl`, `len y = yl`) -/
def mulCQ (xl yl : Nat) : Nat := MCQ (max xl yl) (min xl yl)

theorem mulCQ_comm (xl yl : Nat) : mulCQ xl yl = mulCQ yl xl := by
  unfold mulCQ; rw [Nat.max_comm, Nat.min_comm]

theorem MCQ_eq (m n : Nat) : MCQ m n =
    max (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KCQ n + if n < m then chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) else 0)
    (max (if m = 0 then 0 else MCQ (m - 1) n) (if n = 0 then 0 else MCQ m (n - 1))) := by
  rw [MCQ]; simp only [dite_eq_ite, KCQ]

theorem MCQ_left (m n : Nat) : MCQ m n ≤ MCQ (m + 1) n := by
  rw [MCQ_eq (m + 1) n]; simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]; omega

theorem MCQ_right (m n : Nat) : MCQ m n ≤ MCQ m (n + 1) := by
  rw [MCQ_eq m (n + 1)]; simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]; omega

/-- monotone in both lengths -/
theorem MCQ_len {m n m' n' : Nat} (hm : m ≤ m') (hn : n ≤ n') : MCQ m n ≤ MCQ m' n' := by
  have h1 : ∀ k, MCQ m n ≤ MCQ (m + k) n := by
    intro k; induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (MCQ_left (m + k) n)
  have h2 : ∀ k, MCQ m' n ≤ MCQ m' (n + k) := by
    intro k; induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (MCQ_right m' (n + k))
  have := h1 (m' - m); have := h2 (n' - n)
  rw [show m + (m' - m) = m' by omega] at *; rw [show n + (n' - n) = n' by omega] at *; omega

theorem mulCQ_mono {xl xl' yl yl' : Nat} (h2 : xl ≤ xl') (h3 : yl ≤ yl') : mulCQ xl yl ≤ mulCQ xl' yl' := by
  unfold mulCQ; exact MCQ_len (by omega) (by omega)

/-! ## The paths of `nat.mul(m ≥ n)` -/

theorem MCQ_one {m : Nat} : makeB (m + 1) ≤ MCQ m 1 := by
  rw [MCQ_eq m 1]; simp only [Nat.one_ne_zero, ite_false, ite_true]; omega

theorem MCQ_basic {m n : Nat} (h2 : 2 ≤ n) : makeB (m + n) ≤ MCQ m n := by
  rw [MCQ_eq m n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega)]; omega

/-- `karatsuba(n)` with `m = n` -/
theorem MCQ_kar {n : Nat} (h40 : 40 ≤ n) : makeB (n + n) + KCQ n ≤ MCQ n n := by
  rw [MCQ_eq n n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega),
    if_neg (show ¬ (n < 40 ∨ n < n) by omega), if_neg (show ¬ n < n by omega)]; omega

/-- `karatsuba(n)` and the chunk loop (`n < m`) -/
theorem MCQ_loop {m n : Nat} (h40 : 40 ≤ n) (hm : n < m) :
    makeB (m + n) + KCQ n + chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) ≤ MCQ m n := by
  rw [MCQ_eq m n, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 1 by omega),
    if_neg (show ¬ (n < 40 ∨ m < n) by omega), if_pos hm]; omega

/-- an inner product of `karatsuba(n)` (operands `≤ n2` words) -/
theorem mulCQ_le_inner {n a b : Nat} (ha : a ≤ kh n) (hb : b ≤ kh n) : mulCQ a b ≤ MCQ (kh n) (kh n) := by
  unfold mulCQ; exact MCQ_len (by omega) (by omega)

/-- a chunk product `t.mul(x[i:i+c], y)` (`c ≤ n`) costs exactly the chunk's term -/
theorem mulCQ_chunk {n c : Nat} (hc : c ≤ n) : mulCQ c n = MCQ n (min n c) := by
  unfold mulCQ; rw [Nat.max_eq_right hc, Nat.min_eq_left hc, Nat.min_eq_right hc]

theorem chunkSum_succ (f : Nat → Nat) (n m k : Nat) :
    chunkSum f n m (k + 1) = chunkSum f n m k + f (m - (k + 1) * n) := rfl

/-- the loop's chunks: all full but the last -/
theorem chunkSum_full {n m : Nat} (f : Nat → Nat) :
    ∀ k, (k + 1) * n < m → chunkSum (fun c => f (min n c)) n m k = k * f n := by
  intro k
  induction k with
  | zero => intro _; simp only [chunkSum, Nat.zero_mul]
  | succ k ih =>
    intro hk
    have e : (k + 1 + 1) * n = (k + 1) * n + n := by rw [Nat.add_mul, Nat.one_mul]
    rw [chunkSum_succ, ih (by omega)]
    have : min n (m - (k + 1) * n) = n := Nat.min_eq_left (by omega)
    show k * f n + f (min n (m - (k + 1) * n)) = (k + 1) * f n
    rw [this, Nat.add_mul, Nat.one_mul]

/-- **the chunk loop in closed form**: `(m-1)/n - 1` full chunks and one of `(m-1) % n + 1` words -/
theorem chunkSum_eq {n m : Nat} (f : Nat → Nat) (hn : 0 < n) (hm : n < m) :
    chunkSum (fun c => f (min n c)) n m ((m - 1) / n) = ((m - 1) / n - 1) * f n + f ((m - 1) % n + 1) := by
  have hK : 1 ≤ (m - 1) / n := (Nat.le_div_iff_mul_le hn).2 (by omega)
  have hdm := Nat.div_add_mod (m - 1) n
  have hmod := Nat.mod_lt (m - 1) hn
  obtain ⟨K, hKe⟩ : ∃ K, (m - 1) / n = K + 1 := ⟨(m - 1) / n - 1, by omega⟩
  rw [hKe, chunkSum_succ, chunkSum_full f K ?_]
  · have e1 : m - (K + 1) * n = (m - 1) % n + 1 := by rw [hKe] at hdm; rw [Nat.mul_comm] at hdm; omega
    rw [e1, Nat.min_eq_right (by omega)]; simp only [Nat.add_sub_cancel]
  · rw [hKe] at hdm; rw [Nat.mul_comm] at hdm; omega

/-! ## Squaring -/

/-- `karatsubaSqr(stk, z, x)` with `len x = n` (`basicSqr` for `n < 80`: only `stk.nat(2n)`, free) -/
def ksqrCQ (n : Nat) : Nat :=
  if h : 80 ≤ n then
    3 * asB (2 * ((n + 1) / 2) + 1) + 3 * (makeB (2 * ((n + 1) / 2)) + ksqrCQ ((n + 1) / 2))
  else 0
termination_by n
decreasing_by omega

/-- `z.sqr(stk, x)` with `len x = n` -/
def sqrCQ (n : Nat) : Nat := makeB (2 * n) + if 12 ≤ n then ksqrCQ n else 0

theorem ksqrCQ_big {n : Nat} (h : 80 ≤ n) : ksqrCQ n =
    3 * asB (2 * ((n + 1) / 2) + 1) + 3 * (makeB (2 * ((n + 1) / 2)) + ksqrCQ ((n + 1) / 2)) := by
  rw [ksqrCQ, dif_pos h]

theorem ksqrCQ_small {n : Nat} (h : n < 80) : ksqrCQ n = 0 := by
  rw [ksqrCQ, dif_neg (by omega)]

theorem ksqrCQ_mono : ∀ (n' n : Nat), n ≤ n' → ksqrCQ n ≤ ksqrCQ n' := by
  intro n'
  induction n' using Nat.strongRecOn with
  | _ n' ih =>
    intro n h2
    by_cases hn : 80 ≤ n
    · rw [ksqrCQ_big hn, ksqrCQ_big (n := n') (by omega)]
      have e2 := asB_mono (k := 2 * ((n + 1) / 2) + 1) (k' := 2 * ((n' + 1) / 2) + 1) (by omega)
      have e3 := makeB_mono (k := 2 * ((n + 1) / 2)) (k' := 2 * ((n' + 1) / 2)) (by omega)
      have e4 := ih ((n' + 1) / 2) (by omega) ((n + 1) / 2) (by omega)
      omega
    · rw [ksqrCQ_small (by omega)]; omega

theorem sqrCQ_mono {n n' : Nat} (h2 : n ≤ n') : sqrCQ n ≤ sqrCQ n' := by
  unfold sqrCQ
  have := makeB_mono (k := 2 * n) (k' := 2 * n') (by omega)
  by_cases hn : 12 ≤ n
  · rw [if_pos hn, if_pos (by omega)]; have := ksqrCQ_mono n' n h2; omega
  · rw [if_neg hn]; split <;> omega

theorem sqrCQ_big {n : Nat} (h : 12 ≤ n) : sqrCQ n = makeB (2 * n) + ksqrCQ n := by
  unfold sqrCQ; rw [if_pos h]

/-- an inner `sqr` of `karatsubaSqr(n)` (operand `≤ n2` words) -/
theorem sqrCQ_le_inner {n m : Nat} (hn : 80 ≤ n) (hm : m ≤ (n + 1) / 2) :
    sqrCQ m ≤ makeB (2 * ((n + 1) / 2)) + ksqrCQ ((n + 1) / 2) := by
  have h := sqrCQ_mono hm
  rw [sqrCQ_big (n := (n + 1) / 2) (by omega)] at h; exact h

end FvModexp
