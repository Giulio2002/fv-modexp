import FvModexp.Proofs.Common.Words
/-!
# `divWW` and `reciprocalWord` (arith.go:273-339)

`divWW x1 x0 y m` divides the two-word value `x1*2^64 + x0` (with `x1 < y`) by the word `y`, using the precomputed
approximate reciprocal `m = floor((2^128-1)/d) - 2^64` of the normalised divisor `d = y << nlz y`.
-/
namespace FvModexp.Mdl

/-- The quotient guess of `divWW` (`t1, t0 := bits.Mul(m, x1); _, c := bits.Add(t0, x0, 0); t1, _ = bits.Add(t1, x1, c)`). -/
def qguess (x1 x0 m : Nat) : Nat :=
  let t := m * x1
  let t1 := t / 2 ^ 64
  let t0 := t % 2 ^ 64
  let c := (t0 + x0) / 2 ^ 64
  (t1 + x1 + c) % 2 ^ 64

/-- Remainder computation and the two corrections of `divWW`, given the guess `qq`. -/
def divWWfix (x1 x0 d qq : Nat) : Nat × Nat :=
  let dq := d * qq                                 -- dq1, dq0 := bits.Mul(d, qq)
  let dq1 := dq / 2 ^ 64
  let dq0 := dq % 2 ^ 64
  let r0 := (x0 + 2 ^ 64 - dq0) % 2 ^ 64           -- r0, b := bits.Sub(uint(x0), dq0, 0)
  let b := if x0 < dq0 then 1 else 0
  let r1 := (x1 + 2 ^ 64 - dq1 - b) % 2 ^ 64       -- r1, _ := bits.Sub(uint(x1), dq1, b)
  let qq1 := if r1 ≠ 0 then (qq + 1) % 2 ^ 64 else qq           -- if r1 != 0 { qq++; r0 -= d }
  let r01 := if r1 ≠ 0 then (r0 + 2 ^ 64 - d) % 2 ^ 64 else r0
  if r01 ≥ d then ((qq1 + 1) % 2 ^ 64, (r01 + 2 ^ 64 - d) % 2 ^ 64) else (qq1, r01)  -- if r0 >= d { qq++; r0 -= d }

/-- The normalised body of `divWW` (everything between the `if s != 0 { ... }` block and the final `>> s`). -/
def divWWn (x1 x0 d m : Nat) : Nat × Nat := divWWfix x1 x0 d (qguess x1 x0 m)

/-- arith.go:273 `divWW(x1, x0, y, m)` -> (q, r). -/
def divWW (x1 x0 y m : Nat) : Nat × Nat :=
  let s := nlz y
  let x1' := if s ≠ 0 then ((x1 * 2 ^ s % 2 ^ 64) ||| (x0 / 2 ^ (64 - s))) else x1
  let x0' := if s ≠ 0 then x0 * 2 ^ s % 2 ^ 64 else x0
  let y' := if s ≠ 0 then y * 2 ^ s % 2 ^ 64 else y
  let (q, r) := divWWn x1' x0' y' m
  (q, r / 2 ^ s)

/-- arith.go:333 `reciprocalWord(d1)`: `u := d1 << nlz(d1)`, `bits.Div(^u, _M, u)`. -/
def reciprocalWord (d1 : Nat) : Nat :=
  let u := d1 * 2 ^ nlz d1 % 2 ^ 64
  ((2 ^ 64 - 1 - u) * 2 ^ 64 + (2 ^ 64 - 1)) / u

/-! ### mathematics of the normalised step -/

theorem core_bounds (B d a1 a0 M e qq : Nat) (hB2 : B ≤ 2 * d) (hdB : d < B) (ha1 : a1 < d) (ha0 : a0 < B)
    (hMe : M * d + e = B * B - 1) (hed : e < d) (hq : qq = (M * a1 + a0) / B) :
    qq * d ≤ a1 * B + a0 ∧ a1 * B + a0 < qq * d + B + d := by
  have hB0 : 0 < B := by omega
  have hBB : 1 ≤ B * B := Nat.mul_pos hB0 hB0
  have hN1 := Nat.div_add_mod (M * a1 + a0) B
  have hN2 := Nat.mod_lt (M * a1 + a0) hB0
  rw [← hq] at hN1
  -- N = M*a1 + a0 = B*qq + rem, rem < B
  obtain ⟨rem, hrem⟩ : ∃ rem, rem = (M * a1 + a0) % B := ⟨_, rfl⟩
  rw [← hrem] at hN1 hN2
  -- products
  have hMd : M * a1 * d = a1 * (B * B - 1) - a1 * e := by
    have : M * a1 * d = a1 * (M * d) := by grind
    rw [this]
    have h2 : M * d = B * B - 1 - e := by omega
    rw [h2, Nat.mul_sub]
  have hMdle : a1 * e ≤ a1 * (B * B - 1) := Nat.mul_le_mul_left _ (by omega)
  -- (1) qq * d <= X
  have h1 : qq * d ≤ a1 * B + a0 := by
    have hq1 : qq * B * d ≤ (M * a1 + a0) * d := by
      apply Nat.mul_le_mul_right
      have := Nat.mul_comm qq B
      omega
    have e1 : (M * a1 + a0) * d = M * a1 * d + a0 * d := by grind
    have e2 : a0 * d ≤ a0 * B := Nat.mul_le_mul_left _ (by omega)
    have e3 : a1 * (B * B - 1) + a0 * B < (a1 * B + a0 + 1) * B := by
      have : a1 * (B * B - 1) ≤ a1 * (B * B) := Nat.mul_le_mul_left _ (by omega)
      have e4 : a1 * (B * B) = a1 * B * B := by grind
      have e5 : (a1 * B + a0 + 1) * B = a1 * B * B + a0 * B + B := by grind
      omega
    have : qq * d * B < (a1 * B + a0 + 1) * B := by
      have : qq * d * B = qq * B * d := by grind
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  refine ⟨h1, ?_⟩
  -- (2) X < qq*d + B + d
  by_cases ha : a1 = 0
  · subst ha; simp at *; omega
  · -- B*qq + rem = N, so B*qq*d + rem*d = M*a1*d + a0*d
    have hqd : (qq * d) * B + rem * d = M * a1 * d + a0 * d := by
      have : (B * qq + rem) * d = (M * a1 + a0) * d := by rw [hN1]
      grind
    -- X*B <= qq*d*B + (B-1+...)
    -- want: (a1*B + a0) * B < (qq*d + B + d) * B
    have hr : rem * d ≤ (B - 1) * d := Nat.mul_le_mul_right _ (by omega)
    have hA1 : a1 * (e + 1) ≤ (d - 1) * d := Nat.mul_le_mul (by omega) (by omega)
    have hA0 : a0 * (B - d) ≤ (B - 1) * (B - d) := Nat.mul_le_mul_right _ (by omega)
    -- expand
    have e1 : (a1 * B + a0) * B = a1 * (B * B) + a0 * B := by grind
    have hMd' : M * a1 * d + a1 * e = a1 * (B * B - 1) := by
      have : a1 * (B * B - 1) - a1 * e + a1 * e = a1 * (B * B - 1) := Nat.sub_add_cancel hMdle
      omega
    have e5 : a1 * (B * B - 1) + a1 = a1 * (B * B) := by
      have : a1 * (B * B - 1) + a1 * 1 = a1 * (B * B - 1 + 1) := by grind
      have h3 : B * B - 1 + 1 = B * B := by omega
      rw [h3] at this; omega
    have e6 : a1 * (e + 1) = a1 * e + a1 := by grind
    have e7 : (B - 1) * d + d = B * d := by
      have : (B - 1) * d + 1 * d = (B - 1 + 1) * d := by grind
      have h4 : B - 1 + 1 = B := by omega
      rw [h4] at this; omega
    have e8 : (B - 1) * (B - d) + (B - d) = B * (B - d) := by
      have : (B - 1) * (B - d) + 1 * (B - d) = (B - 1 + 1) * (B - d) := by grind
      have h4 : B - 1 + 1 = B := by omega
      rw [h4] at this; omega
    have e9 : B * (B - d) + B * d = B * B := by
      have : B * (B - d) + B * d = B * (B - d + d) := by grind
      have h4 : B - d + d = B := by omega
      rw [h4] at this; omega
    have e10 : (d - 1) * d + d = d * d := by
      have : (d - 1) * d + 1 * d = (d - 1 + 1) * d := by grind
      have h4 : d - 1 + 1 = d := by omega
      rw [h4] at this; omega
    have hdd : d * d ≤ d * B := Nat.mul_le_mul_left _ (by omega)
    have e11 : (qq * d + B + d) * B = qq * d * B + B * B + d * B := by grind
    have e12 : a0 * B = a0 * d + a0 * (B - d) := by
      have : a0 * d + a0 * (B - d) = a0 * (d + (B - d)) := by grind
      have h4 : d + (B - d) = B := by omega
      rw [h4] at this; omega
    have hdBc : d * B = B * d := Nat.mul_comm _ _
    -- main inequality: (a1*B+a0)*B < (qq*d+B+d)*B
    have : (a1 * B + a0) * B < (qq * d + B + d) * B := by
      rw [e1, e11]
      omega
    exact Nat.lt_of_mul_lt_mul_right this


theorem qguess_eq (x1 x0 m : Nat) : qguess x1 x0 m = ((m + 2 ^ 64) * x1 + x0) / 2 ^ 64 % 2 ^ 64 := by
  unfold qguess
  simp only []
  have : (m + 2 ^ 64) * x1 = m * x1 + 2 ^ 64 * x1 := by rw [Nat.add_mul, Nat.mul_comm (2 ^ 64) x1]
  rw [this]
  generalize m * x1 = t
  omega

theorem divWWfix_spec (x1 x0 d qq : Nat) (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hx1 : x1 < d) (hx0 : x0 < 2 ^ 64)
    (h1 : qq * d ≤ x1 * 2 ^ 64 + x0) (h2 : x1 * 2 ^ 64 + x0 < qq * d + 2 ^ 64 + d) :
    divWWfix x1 x0 d qq = ((x1 * 2 ^ 64 + x0) / d, (x1 * 2 ^ 64 + x0) % d) := by
  unfold divWWfix
  simp only []
  have hd0 : 0 < d := by omega
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (x1 * 2 ^ 64 + x0) / d := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (x1 * 2 ^ 64 + x0) % d := ⟨_, rfl⟩
  have hX := Nat.div_add_mod (x1 * 2 ^ 64 + x0) d
  have hRd : R < d := by rw [hR]; exact Nat.mod_lt _ hd0
  rw [← hQ, ← hR] at hX
  rw [← hQ, ← hR]
  have hdQ : d * Q = Q * d := Nat.mul_comm _ _
  have hdq : d * qq = qq * d := Nat.mul_comm _ _
  have hqQ : qq ≤ Q := by
    rw [hQ]; exact (Nat.le_div_iff_mul_le hd0).2 h1
  have hQq : Q ≤ qq + 2 := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have : (qq + 3) * d ≤ Q * d := Nat.mul_le_mul_right _ hlt
    have e : (qq + 3) * d = qq * d + 3 * d := by grind
    omega
  rw [hdq]
  have hQB : Q < 2 ^ 64 := by
    refine Nat.lt_of_mul_lt_mul_right (a := d) ?_
    have : Q * d ≤ x1 * 2 ^ 64 + x0 := by omega
    have : x1 * 2 ^ 64 + x0 < d * 2 ^ 64 := by
      have : (x1 + 1) * 2 ^ 64 ≤ d * 2 ^ 64 := Nat.mul_le_mul_right _ hx1
      rw [Nat.add_mul] at this; omega
    omega
  rcases (by omega : Q = qq ∨ Q = qq + 1 ∨ Q = qq + 2) with hk | hk | hk
  · have e1 : Q * d = qq * d := by rw [hk]
    refine Prod.ext ?_ ?_ <;> (simp only []; repeat' split) <;> omega
  · have e1 : Q * d = qq * d + d := by rw [hk]; grind
    refine Prod.ext ?_ ?_ <;> (simp only []; repeat' split) <;> omega
  · have e1 : Q * d = qq * d + 2 * d := by rw [hk]; grind
    refine Prod.ext ?_ ?_ <;> (simp only []; repeat' split) <;> omega


theorem divWWn_spec (x1 x0 d m : Nat) (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hx1 : x1 < d) (hx0 : x0 < 2 ^ 64)
    (hm : m + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / d) :
    divWWn x1 x0 d m = ((x1 * 2 ^ 64 + x0) / d, (x1 * 2 ^ 64 + x0) % d) := by
  unfold divWWn
  have hd0 : 0 < d := by omega
  have hMe := Nat.div_add_mod (2 ^ 64 * 2 ^ 64 - 1) d
  have hed : (2 ^ 64 * 2 ^ 64 - 1) % d < d := Nat.mod_lt _ hd0
  rw [← hm] at hMe
  have hMe' : (m + 2 ^ 64) * d + (2 ^ 64 * 2 ^ 64 - 1) % d = 2 ^ 64 * 2 ^ 64 - 1 := by
    rw [Nat.mul_comm]; exact hMe
  obtain ⟨hb1, hb2⟩ := core_bounds (2 ^ 64) d x1 x0 (m + 2 ^ 64) _ (((m + 2 ^ 64) * x1 + x0) / 2 ^ 64)
    (by omega) hd2 hx1 hx0 hMe' hed rfl
  have hqB : ((m + 2 ^ 64) * x1 + x0) / 2 ^ 64 < 2 ^ 64 := by
    refine Nat.lt_of_mul_lt_mul_right (a := d) ?_
    have : x1 * 2 ^ 64 + x0 < d * 2 ^ 64 := by
      have : (x1 + 1) * 2 ^ 64 ≤ d * 2 ^ 64 := Nat.mul_le_mul_right _ hx1
      rw [Nat.add_mul] at this; omega
    omega
  rw [qguess_eq, Nat.mod_eq_of_lt hqB]
  exact divWWfix_spec x1 x0 d _ hd1 hd2 hx1 hx0 hb1 hb2

/-- Normalisation of a division: `U*t = D*t*Q + Rn`, `Rn < D*t` gives `Q = U/D`, `Rn = (U%D)*t`. -/
theorem norm_div (U D t Q Rn : Nat) (ht : 0 < t) (hD : 0 < D) (h : U * t = D * t * Q + Rn) (hR : Rn < D * t) :
    Q = U / D ∧ Rn = (U % D) * t := by
  have h1 : D * Q * t ≤ U * t := by
    have : D * Q * t = D * t * Q := by grind
    omega
  have h2 : D * Q ≤ U := Nat.le_of_mul_le_mul_right h1 ht
  obtain ⟨r, hr⟩ : ∃ r, U = D * Q + r := ⟨U - D * Q, by omega⟩
  have h3 : Rn = r * t := by
    have : U * t = D * Q * t + r * t := by rw [hr]; grind
    have e : D * Q * t = D * t * Q := by grind
    omega
  have h4 : r < D := by
    have : r * t < D * t := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hq := (Nat.div_mod_unique (a := U) (b := D) (d := Q) (c := r) hD).2 ⟨by omega, h4⟩
  obtain ⟨hq1, hq2⟩ := hq
  exact ⟨hq1.symm, by rw [hq2, h3]⟩

/-- Correctness of `divWW`: with `m` the reciprocal of the normalised divisor, `(q, r) = (X / y, X % y)` for `X = x1*2^64 + x0`. -/
theorem divWW_spec (x1 x0 y m : Nat) (hy : 0 < y) (hyB : y < 2 ^ 64) (hx1 : x1 < y) (hx0 : x0 < 2 ^ 64)
    (hm : m + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / (y * 2 ^ nlz y)) :
    divWW x1 x0 y m = ((x1 * 2 ^ 64 + x0) / y, (x1 * 2 ^ 64 + x0) % y) := by
  unfold divWW
  obtain ⟨hs63, hs1, hs2⟩ := nlz_spec y hy hyB
  generalize nlz y = s at *
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have hlo2 : x0 / 2 ^ (64 - s) < 2 ^ s := by
    have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    apply Nat.div_lt_of_lt_mul
    rw [← e]; exact hx0
  have hhi2 : x1 * 2 ^ s < 2 ^ 64 := by
    have : (x1 + 1) * 2 ^ s ≤ y * 2 ^ s := Nat.mul_le_mul_right _ hx1
    rw [Nat.add_mul] at this; omega
  -- uniform description of the shifted operands (also for s = 0)
  have hx1a : (if s ≠ 0 then ((x1 * 2 ^ s % 2 ^ 64) ||| (x0 / 2 ^ (64 - s))) else x1) = x1 * 2 ^ s + x0 / 2 ^ (64 - s) := by
    by_cases h0 : s = 0
    · subst h0; simp; omega
    · rw [if_pos h0, Nat.mod_eq_of_lt hhi2, Nat.mul_comm x1 (2 ^ s), ← Nat.two_pow_add_eq_or_of_lt hlo2 x1, Nat.mul_comm (2 ^ s) x1]
  have hx0a : (if s ≠ 0 then x0 * 2 ^ s % 2 ^ 64 else x0) = x0 * 2 ^ s % 2 ^ 64 := by
    by_cases h0 : s = 0
    · subst h0; simp; omega
    · rw [if_pos h0]
  have hya : (if s ≠ 0 then y * 2 ^ s % 2 ^ 64 else y) = y * 2 ^ s := by
    by_cases h0 : s = 0
    · subst h0; simp
    · rw [if_pos h0, Nat.mod_eq_of_lt hs1]
  simp only [hx1a, hx0a, hya]
  have hsplit : x0 * 2 ^ s = (x0 / 2 ^ (64 - s)) * 2 ^ 64 + x0 * 2 ^ s % 2 ^ 64 := by
    have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    have hq : x0 * 2 ^ s / 2 ^ 64 = x0 / 2 ^ (64 - s) := by
      rw [e, Nat.mul_comm (2 ^ (64 - s)), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hp]
    have := Nat.div_add_mod (x0 * 2 ^ s) (2 ^ 64)
    rw [hq] at this
    omega
  have hU : (x1 * 2 ^ 64 + x0) * 2 ^ s =
      (x1 * 2 ^ s + x0 / 2 ^ (64 - s)) * 2 ^ 64 + x0 * 2 ^ s % 2 ^ 64 := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64) (2 ^ s), ← Nat.mul_assoc, hsplit]
    grind
  have ha1 : x1 * 2 ^ s + x0 / 2 ^ (64 - s) < y * 2 ^ s := by
    have : (x1 + 1) * 2 ^ s ≤ y * 2 ^ s := Nat.mul_le_mul_right _ hx1
    rw [Nat.add_mul] at this; omega
  have hmod : x0 * 2 ^ s % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  have := divWWn_spec (x1 * 2 ^ s + x0 / 2 ^ (64 - s)) (x0 * 2 ^ s % 2 ^ 64) (y * 2 ^ s) m hs2 hs1 ha1 hmod hm
  rw [this]
  rw [← hU]
  have hnd := norm_div (x1 * 2 ^ 64 + x0) y (2 ^ s) ((x1 * 2 ^ 64 + x0) * 2 ^ s / (y * 2 ^ s))
    ((x1 * 2 ^ 64 + x0) * 2 ^ s % (y * 2 ^ s)) hp hy (by
      have hh := Nat.div_add_mod ((x1 * 2 ^ 64 + x0) * 2 ^ s) (y * 2 ^ s)
      rw [← hh]; grind) (Nat.mod_lt _ (by omega))
  refine Prod.ext ?_ ?_
  · exact hnd.1
  · show (x1 * 2 ^ 64 + x0) * 2 ^ s % (y * 2 ^ s) / 2 ^ s = (x1 * 2 ^ 64 + x0) % y
    rw [hnd.2, Nat.mul_div_cancel _ hp]

theorem recip_arith (N B u : Nat) (hu : 0 < u) (hle : u * B ≤ N) : (N - u * B) / u + B = N / u := by
  have h1 := Nat.add_mul_div_left (N - u * B) B hu
  have h2 : N - u * B + u * B = N := by omega
  rw [h2] at h1; exact h1.symm

theorem recip_core (B u : Nat) (hu : 0 < u) (huB : u < B) :
    ((B - 1 - u) * B + (B - 1)) / u + B = (B * B - 1) / u := by
  have hle : u * B ≤ B * B - 1 := by
    have : (u + 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
    rw [Nat.add_mul] at this; omega
  have e : (B - 1 - u) * B = B * B - B - u * B := by
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul]
  have hB1 : B ≤ B * B := Nat.le_mul_self B
  have hle2 : u * B + B ≤ B * B := by
    have : (u + 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
    rw [Nat.add_mul] at this; omega
  have e1 : (B - 1 - u) * B + (B - 1) = (B * B - 1) - u * B := by omega
  rw [e1]
  exact recip_arith _ _ u hu hle

/-- `reciprocalWord(d1)` is the reciprocal `floor((2^128-1)/u) - 2^64` of the normalised divisor `u = d1 << nlz d1`. -/
theorem reciprocalWord_spec (d1 : Nat) (h0 : 0 < d1) (h : d1 < 2 ^ 64) :
    reciprocalWord d1 + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / (d1 * 2 ^ nlz d1) := by
  unfold reciprocalWord
  obtain ⟨hs63, hs1, hs2⟩ := nlz_spec d1 h0 h
  generalize nlz d1 = s at *
  simp only []
  rw [Nat.mod_eq_of_lt hs1]
  generalize d1 * 2 ^ s = u at *
  exact recip_core (2 ^ 64) u (by omega) hs1

end FvModexp.Mdl
