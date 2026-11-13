import FvModexp.Proofs.Common.MulCostQ

set_option autoImplicit false

/-!
# Closed per-level upper bounds of the level-free mul/sqr budgets (divmc s37; TIGHT COSTS / BudOK)

`MCQ m n` (Common/MulCostQ) is a recursive max over all the paths of `nat.mul`; the BudOK proof needs closed
LINEAR bounds. Linear bounds valid for every size do not exist (karatsuba is `n^1.58`) and a single slope in the
long operand `m` cannot reproduce itself through the chunk loop (each chunk re-pays the `n`-word square plus
the outer `makeB(m+n)`), so the bounds are PER LEVEL of the short operand `n` (the karatsuba recursion depth),
in two families proved together:
* the **box** `MCQ m' n' ≤ D·n + E` for all `m', n' ≤ n` (squares, and everything `MCQ n n` maxes over);
* the **P-form** `MCQ m n ≤ A·m + B·n + C` for `n ≤ m` (rectangles: `A` pays one square chunk per `n` words
  of `m` plus the outer `makeB`; `B`, `C` the once-per-call `karatsuba(n)`).
Levels: `n < 40` (basicMul), `n < 79` (`kh n < 40`: one karatsuba level), `n < 157` (two levels). Numbers
(scratchpad mirror; exact `MCQ`): the box is within 1.13× / 1.5× of the real square cost on levels 1 / 2;
with these bounds substituted for `mulCQ`/`sqrCQ` the full BudOK mirror (2.13 M points) still passes (worst
ratio 0.82 against the factor-free ExpBudget). Every size the BudOK needs has the short operand `≤ 129`.
`sqrCQ` gets the same treatment (one simple recursion, three levels: `n < 80 / 158 / 315`).
-/

namespace FvModexp

theorem makeB_eq (k : Nat) : makeB k = 16 * k + 88 := by unfold makeB allocCost; omega
theorem asB_eq (k : Nat) : asB k = 16 * k + 104 := by unfold asB allocCost; omega

/-- the `a`-branch (own path) of `MCQ m n` -/
private theorem MCQ_split {m n : Nat} {X : Nat}
    (ha : (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KCQ n + if n < m then chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) else 0) ≤ X)
    (h1 : m ≠ 0 → MCQ (m - 1) n ≤ X) (h2 : n ≠ 0 → MCQ m (n - 1) ≤ X) : MCQ m n ≤ X := by
  rw [MCQ_eq]
  refine Nat.max_le.2 ⟨ha, Nat.max_le.2 ⟨?_, ?_⟩⟩
  · split
    · exact Nat.zero_le _
    · exact h1 (by assumption)
  · split
    · exact Nat.zero_le _
    · exact h2 (by assumption)

/-- the own path when it is a plain `basicMul` (`n < 40` or `m < n`) or `mulAddWW` / nothing -/
private theorem MCQ_own_plain {m n X : Nat} (hp : n < 40 ∨ m < n) (h1 : n = 1 → 16 * m + 104 ≤ X)
    (h2 : 2 ≤ n → 16 * (m + n) + 88 ≤ X) :
    (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KCQ n + if n < m then chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) else 0) ≤ X := by
  by_cases e0 : n = 0
  · rw [if_pos e0]; exact Nat.zero_le _
  rw [if_neg e0]
  by_cases e1 : n = 1
  · rw [if_pos e1, makeB_eq]; have := h1 e1; omega
  rw [if_neg e1, if_pos hp, makeB_eq]; have := h2 (by omega); omega

/-- the own path of a karatsuba-sized call (`40 ≤ n ≤ m`): square (`m = n`) or square + chunk loop -/
private theorem MCQ_own_kar {m n X : Nat} (h40 : 40 ≤ n) (hnm : n ≤ m)
    (hsq : m = n → 16 * (m + n) + 88 + KCQ n ≤ X)
    (hch : n < m → 16 * (m + n) + 88 + KCQ n +
      (((m - 1) / n - 1) * MCQ n n + MCQ n ((m - 1) % n + 1)) ≤ X) :
    (if n = 0 then 0 else if n = 1 then makeB (m + 1) else
        makeB (m + n) + if n < 40 ∨ m < n then 0 else
          KCQ n + if n < m then chunkSum (fun c => MCQ n (min n c)) n m ((m - 1) / n) else 0) ≤ X := by
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), makeB_eq]
  by_cases hm : n < m
  · rw [if_pos hm, chunkSum_eq (MCQ n) (by omega) hm]; have := hch hm; omega
  · rw [if_neg hm]; have := hsq (by omega); omega

/-! ## Level 0: `n < 40` (no karatsuba) -/

/-- **level 0**: `MCQ m n ≤ 16(m + n) + 88` when `n < 40` (any `m`) -/
theorem MCQ_P0 (m n : Nat) (hn : n < 40) : MCQ m n ≤ 16 * m + 16 * n + 88 := by
  apply MCQ_split (MCQ_own_plain (Or.inl hn) (fun _ => by omega) (fun _ => by omega))
  · intro _; have := MCQ_P0 (m - 1) n hn; omega
  · intro _; have := MCQ_P0 m (n - 1) (by omega); omega
termination_by m + n

/-- a call with `m < n` takes the plain path; its `MCQ` is bounded by any symmetric-enough bound -/
theorem MCQ_P0' (m n : Nat) (hm : m < 40) : MCQ m n ≤ 16 * m + 16 * n + 88 := by
  apply MCQ_split
  · by_cases h : n < 40 ∨ m < n
    · exact MCQ_own_plain h (fun _ => by omega) (fun _ => by omega)
    · omega
  · intro _; have := MCQ_P0' (m - 1) n (by omega); omega
  · intro _; have := MCQ_P0' m (n - 1) hm; omega
termination_by m + n

/-! ## The karatsuba step `KCQ n` from the box of the level below -/

theorem KCQ_le {n D E : Nat} (hbox : MCQ (kh n) (kh n) ≤ D * kh n + E) :
    KCQ n ≤ 128 * kh n + 480 + 3 * (D * kh n) + 3 * E := by
  unfold KCQ; rw [asB_eq]
  have : 3 * MCQ (kh n) (kh n) ≤ 3 * (D * kh n + E) := Nat.mul_le_mul_left 3 hbox
  omega

/-! ## Level 1: `n < 79` -/

theorem box0 {m' n' n : Nat} (h1 : m' ≤ n) (h2 : n' ≤ n) (h : n < 40) : MCQ m' n' ≤ 32 * n + 88 := by
  have := MCQ_P0 m' n' (by omega); omega

theorem KCQ_le1 {n : Nat} (h : n < 79) : KCQ n ≤ 112 * n + 856 := by
  have hk : kh n < 40 := by unfold kh; omega
  have hb : MCQ (kh n) (kh n) ≤ 32 * kh n + 88 := box0 (Nat.le_refl _) (Nat.le_refl _) hk
  have := KCQ_le hb
  have hk2 : kh n * 2 ≤ n + 1 := Nat.div_mul_le_self (n + 1) 2
  generalize kh n = k at *
  omega

/-- **level-1 box**: `MCQ m' n' ≤ 160 n + 1032` for `m', n' ≤ n < 79` -/
theorem box1 (m' n' n : Nat) (h1 : m' ≤ n) (h2 : n' ≤ n) (h : n < 79) : MCQ m' n' ≤ 160 * n + 1032 := by
  by_cases hlo : n' < 40
  · have := MCQ_P0 m' n' hlo; omega
  by_cases hlo' : m' < 40
  · have := MCQ_P0' m' n' hlo'; omega
  apply MCQ_split
  · by_cases hp : m' < n'
    · exact MCQ_own_plain (Or.inr hp) (fun _ => by omega) (fun _ => by omega)
    · refine MCQ_own_kar (by omega) (by omega) ?_ ?_
      · intro _; have := KCQ_le1 (n := n') (by omega); omega
      · intro hlt
        -- one chunk: `(m'-1)/n' = 1`, remainder `r = m' - n' < 40`
        have hK : (m' - 1) / n' = 1 := by
          rw [Nat.div_eq_iff (by omega)]; omega
        have hr : (m' - 1) % n' + 1 = m' - n' := by
          have := Nat.div_add_mod (m' - 1) n'; rw [hK, Nat.mul_one] at this; omega
        rw [hK, hr, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
        have := MCQ_P0 n' (m' - n') (by omega)
        have := KCQ_le1 (n := n') (by omega); omega
  · intro _; exact box1 (m' - 1) n' n (by omega) h2 h
  · intro _; exact box1 m' (n' - 1) n h1 (by omega) h
termination_by m' + n'

/-- the chunk loop arithmetic: `K` chunks of at most `D n + E` each (`K n ≤ m - 1`, `N ≤ n`) -/
private theorem chunks_le {m n K X Y D E N c : Nat} (hK1 : 1 ≤ K) (hKn : K * n ≤ m - 1) (hN : N ≤ n)
    (hc : E ≤ c * N) (hX : X ≤ D * n + E) (hY : Y ≤ D * n + E) :
    (K - 1) * X + Y ≤ D * (m - 1) + c * (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e1 : k * X ≤ k * (D * n + E) := Nat.mul_le_mul_left k hX
  have e2 : (k + 1) * N ≤ (k + 1) * n := Nat.mul_le_mul_left _ hN
  have e3 : (k + 1) * E ≤ (k + 1) * (c * N) := Nat.mul_le_mul_left _ hc
  have e4 : D * ((k + 1) * n) ≤ D * (m - 1) := Nat.mul_le_mul_left D hKn
  have e5 : c * ((k + 1) * N) ≤ c * (m - 1) := Nat.mul_le_mul_left c (Nat.le_trans e2 hKn)
  have r1 : k * (D * n + E) + (D * n + E) = D * ((k + 1) * n) + (k + 1) * E := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; ac_rfl
  have r2 : (k + 1) * (c * N) = c * ((k + 1) * N) := by ac_rfl
  omega

/-- **level-1 P-form**: `MCQ m n ≤ 202 m + 128 n + 944` for `n ≤ m`, `n < 79` -/
theorem MCQ_P1 (m n : Nat) (hnm : n ≤ m) (hn : n < 79) : MCQ m n ≤ 202 * m + 128 * n + 944 := by
  by_cases hlo : n < 40
  · have := MCQ_P0 m n hlo; omega
  apply MCQ_split
  · refine MCQ_own_kar (by omega) hnm ?_ ?_
    · intro _; have := KCQ_le1 (n := n) hn; omega
    · intro hlt
      have hK1 : 1 ≤ (m - 1) / n := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have hKn : (m - 1) / n * n ≤ m - 1 := Nat.div_mul_le_self _ _
      have hrn : (m - 1) % n + 1 ≤ n := Nat.mod_lt _ (by omega)
      have := chunks_le (N := 40) (c := 26) hK1 hKn (by omega) (by omega)
        (box1 n n n (Nat.le_refl _) (Nat.le_refl _) hn) (box1 n ((m - 1) % n + 1) n (Nat.le_refl _) hrn hn)
      have := KCQ_le1 (n := n) hn; omega
  · intro _
    by_cases h : n ≤ m - 1
    · have := MCQ_P1 (m - 1) n h hn; omega
    · have := box1 (m - 1) n n (by omega) (Nat.le_refl _) hn; omega
  · intro _; have := MCQ_P1 m (n - 1) (by omega) (by omega); omega
termination_by m + n

/-! ## Level 2: `n < 157` -/

theorem KCQ_le2 {n : Nat} (h : n < 157) : KCQ n ≤ 304 * n + 3880 := by
  have hk : kh n < 79 := by unfold kh; omega
  have hb : MCQ (kh n) (kh n) ≤ 160 * kh n + 1032 := box1 (kh n) (kh n) (kh n) (Nat.le_refl _) (Nat.le_refl _) hk
  have := KCQ_le hb
  have hk2 : kh n * 2 ≤ n + 1 := Nat.div_mul_le_self (n + 1) 2
  generalize kh n = k at *
  omega

/-- `MCQ` with the short side `< 79` (either order), via the P-form -/
theorem MCQ_P1' (m n : Nat) (hnm : m ≤ n) (hm : m < 79) : MCQ m n ≤ 202 * n + 128 * m + 944 := by
  by_cases hlo : m < 40
  · have := MCQ_P0' m n hlo; omega
  apply MCQ_split
  · by_cases hp : m < n
    · exact MCQ_own_plain (Or.inr hp) (fun _ => by omega) (fun _ => by omega)
    · -- `m = n`: the square
      refine MCQ_own_kar (by omega) (by omega) ?_ (fun h => absurd h (by omega))
      intro _; have := KCQ_le1 (n := n) (by omega); omega
  · intro _; have := MCQ_P1' (m - 1) n (by omega) (by omega); omega
  · intro _
    by_cases h : m ≤ n - 1
    · have := MCQ_P1' m (n - 1) h hm; omega
    · have := MCQ_P1 m (n - 1) (by omega) (by omega); omega
termination_by m + n

/-- **level-2 box**: `MCQ m' n' ≤ 538 n + 4912` for `m', n' ≤ n < 157` -/
theorem box2 (m' n' n : Nat) (h1 : m' ≤ n) (h2 : n' ≤ n) (h : n < 157) : MCQ m' n' ≤ 538 * n + 4912 := by
  by_cases hlo : n' < 79
  · by_cases hle : n' ≤ m'
    · have := MCQ_P1 m' n' hle hlo; omega
    · have := MCQ_P1' m' n' (by omega) (by omega); omega
  by_cases hlo' : m' < 79
  · have := MCQ_P1' m' n' (by omega) hlo'; omega
  apply MCQ_split
  · by_cases hp : m' < n'
    · exact MCQ_own_plain (Or.inr hp) (fun _ => by omega) (fun _ => by omega)
    · refine MCQ_own_kar (by omega) (by omega) ?_ ?_
      · intro _; have := KCQ_le2 (n := n') (by omega); omega
      · intro hlt
        have hK : (m' - 1) / n' = 1 := by
          rw [Nat.div_eq_iff (by omega)]; omega
        have hr : (m' - 1) % n' + 1 = m' - n' := by
          have := Nat.div_add_mod (m' - 1) n'; rw [hK, Nat.mul_one] at this; omega
        rw [hK, hr, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
        have := MCQ_P1 n' (m' - n') (by omega) (by omega)
        have := KCQ_le2 (n := n') (by omega); omega
  · intro _; exact box2 (m' - 1) n' n (by omega) h2 h
  · intro _; exact box2 m' (n' - 1) n h1 (by omega) h
termination_by m' + n'

/-- **level-2 P-form**: `MCQ m n ≤ 617 m + 320 n + 3968` for `n ≤ m`, `n < 157` -/
theorem MCQ_P2 (m n : Nat) (hnm : n ≤ m) (hn : n < 157) : MCQ m n ≤ 617 * m + 320 * n + 3968 := by
  by_cases hlo : n < 79
  · have := MCQ_P1 m n hnm hlo; omega
  apply MCQ_split
  · refine MCQ_own_kar (by omega) hnm ?_ ?_
    · intro _; have := KCQ_le2 (n := n) hn; omega
    · intro hlt
      have hK1 : 1 ≤ (m - 1) / n := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have hKn : (m - 1) / n * n ≤ m - 1 := Nat.div_mul_le_self _ _
      have hrn : (m - 1) % n + 1 ≤ n := Nat.mod_lt _ (by omega)
      have := chunks_le (N := 79) (c := 63) hK1 hKn (by omega) (by omega)
        (box2 n n n (Nat.le_refl _) (Nat.le_refl _) hn) (box2 n ((m - 1) % n + 1) n (Nat.le_refl _) hrn hn)
      have := KCQ_le2 (n := n) hn; omega
  · intro _
    by_cases h : n ≤ m - 1
    · have := MCQ_P2 (m - 1) n h hn; omega
    · have := box2 (m - 1) n n (by omega) (Nat.le_refl _) hn; omega
  · intro _; have := MCQ_P2 m (n - 1) (by omega) (by omega); omega
termination_by m + n

/-! ## Exports for the BudOK: `mulCQ` -/

/-- the per-level closed bound of `mulCQ` (`M` = long side, `n` = short side `< 157`) -/
def mulCB (M n : Nat) : Nat :=
  if n < 40 then 16 * M + 16 * n + 88 else if n < 79 then 202 * M + 128 * n + 944 else 617 * M + 320 * n + 3968

theorem mulCQ_le_B {xl yl : Nat} (h : min xl yl < 157) : mulCQ xl yl ≤ mulCB (max xl yl) (min xl yl) := by
  unfold mulCQ mulCB
  have hle : min xl yl ≤ max xl yl := by omega
  split
  · exact MCQ_P0 _ _ (by assumption)
  · split
    · exact MCQ_P1 _ _ hle (by assumption)
    · exact MCQ_P2 _ _ hle h

/-- squares (`xl, yl ≤ n`): the box -/
theorem mulCQ_le_box {xl yl n : Nat} (h1 : xl ≤ n) (h2 : yl ≤ n) (h : n < 157) :
    mulCQ xl yl ≤ 538 * n + 4912 := by
  unfold mulCQ; exact box2 _ _ _ (by omega) (by omega) h

theorem mulCQ_le_box1 {xl yl n : Nat} (h1 : xl ≤ n) (h2 : yl ≤ n) (h : n < 79) :
    mulCQ xl yl ≤ 160 * n + 1032 := by
  unfold mulCQ; exact box1 _ _ _ (by omega) (by omega) h

/-- **`mulCQ ≤ 0.36 · opCost`** on squares `≤ n < 157` (`opCost n = allocCost (1024 n + 1024)`, Top/RunIface) -/
theorem mulCQ_le_op {xl yl n : Nat} (h1 : xl ≤ n) (h2 : yl ≤ n) (h : n < 157) :
    100 * mulCQ xl yl ≤ 36 * allocCost (1024 * n + 1024) := by
  unfold allocCost
  by_cases h40 : n < 40
  · have := MCQ_P0 (max xl yl) (min xl yl) (by omega); unfold mulCQ; omega
  by_cases h79 : n < 79
  · have := mulCQ_le_box1 h1 h2 h79; omega
  · have := mulCQ_le_box h1 h2 h; omega

/-! ## `sqrCQ` -/

theorem ksqrCQ_le1 {n : Nat} (h : n < 158) : ksqrCQ n ≤ 96 * n + 720 := by
  by_cases h80 : 80 ≤ n
  · rw [ksqrCQ_big h80, ksqrCQ_small (by omega), asB_eq, makeB_eq]; omega
  · rw [ksqrCQ_small (by omega)]; omega

theorem ksqrCQ_le2 {n : Nat} (h : n < 315) : ksqrCQ n ≤ 240 * n + 3024 := by
  by_cases h80 : 80 ≤ n
  · rw [ksqrCQ_big h80, asB_eq, makeB_eq]; have := ksqrCQ_le1 (n := (n + 1) / 2) (by omega); omega
  · rw [ksqrCQ_small (by omega)]; omega

/-- the per-level closed bound of `sqrCQ` -/
def sqrCB (n : Nat) : Nat := if n < 80 then 32 * n + 88 else if n < 158 then 128 * n + 808 else 272 * n + 3112

theorem sqrCQ_le_B {n : Nat} (h : n < 315) : sqrCQ n ≤ sqrCB n := by
  unfold sqrCQ sqrCB; rw [makeB_eq]
  by_cases h80 : n < 80
  · rw [if_pos h80, ksqrCQ_small h80]; split <;> omega
  rw [if_neg h80, if_pos (show 12 ≤ n by omega)]
  by_cases h158 : n < 158
  · rw [if_pos h158]; have := ksqrCQ_le1 h158; omega
  · rw [if_neg h158]; have := ksqrCQ_le2 h; omega

/-- **`sqrCQ ≤ 0.14 · opCost`** for `n < 158` -/
theorem sqrCQ_le_op {n : Nat} (h : n < 158) : 100 * sqrCQ n ≤ 14 * allocCost (1024 * n + 1024) := by
  have := sqrCQ_le_B (n := n) (by omega); unfold sqrCB at this; unfold allocCost
  split at this <;> omega

end FvModexp
