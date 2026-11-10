import Janus

/-!
# Mathematics of the word division `divWW` (go-bigmodexpfix `src/math/big/arith.go:273-330`), ISA independent

Everything is a plain `Nat` statement.  `B = 2^64`; `d` is the normalised divisor (`y << nlz(y)`, `B/2 <= d < B`), the
dividend is `X1 * B + X0` with `X1 < d`, and `m = floor((B^2-1)/d) - B` is the reciprocal of `reciprocalWord`
(arith.go:333).  The comments of arith.go (lines 280-330) argue:

* `t1 = floor((m*X1 + X0)/B) + X1` (arith.go:303-306: `bits.Mul`, `bits.Add(t0,x0,0)`, `bits.Add(t1,x1,c)`) is the
  quotient estimate: `d*t1 <= X` (it is never too large) and `X < d*t1 + B + d` (the remainder is `< B + d`,
  arith.go:314-327);
* the two corrections (arith.go:333-343 `if r1 != 0 {qq++; r0 -= d}`, `if r0 >= d {qq++; r0 -= d}`) make the
  estimate exact: quotient `X / d`, remainder `X % d`.
-/

namespace FvModexp.AsmDiv

/-- `recipWord y = floor((2^128-1) / (y << nlz y)) - 2^64`: the value `reciprocalWord(y)` returns (arith.go:333-339,
`rec, _ := bits.Div(^u, _M, u)`), for `y != 0`. -/
def recipWord (y : Nat) : Nat := (2 ^ 128 - 1) / (y * 2 ^ Janus.Arm64.clzNat 64 y) - 2 ^ 64

/-- (arith.go:280-306) The estimate `t1` is below `B`, never above the true quotient, and the remainder `X - d*t1`
is below `B + d` (generic in the word base `B`, `d < B`). -/
theorem estimate_gen (B d X1 X0 m t1 : Nat) (hB : 0 < B) (hd0 : 0 < d) (hd2 : d < B) (hX1 : X1 < d) (hX0 : X0 < B)
    (hm : m = (B * B - 1) / d - B) (ht : t1 = (m * X1 + X0) / B + X1) :
    t1 < B ∧ d * t1 ≤ X1 * B + X0 ∧ X1 * B + X0 < d * t1 + B + d := by
  have hBB : 1 ≤ B * B := Nat.mul_pos hB hB
  have hM1 : ((B * B - 1) / d) * d ≤ B * B - 1 := Nat.div_mul_le_self _ _
  have hM2 : B * B - 1 < ((B * B - 1) / d) * d + d := by
    have := Nat.lt_div_mul_add (a := B * B - 1) hd0
    simpa [Nat.mul_comm] using this
  have hMB : B ≤ (B * B - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_right B (show d + 1 ≤ B by omega)
    rw [Nat.add_mul] at this
    rw [Nat.mul_comm]
    omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = (B * B - 1) / d := ⟨_, rfl⟩
  rw [← hMdef] at hM1 hM2 hMB hm
  have hmM : M = m + B := by omega
  have hmx : m * X1 + X1 * B = M * X1 := by
    rw [hmM, Nat.add_mul, Nat.mul_comm X1]
  have ht' : t1 = (M * X1 + X0) / B := by
    have e : (m * X1 + X0 + X1 * B) / B = (m * X1 + X0) / B + X1 := Nat.add_mul_div_right _ _ hB
    rw [ht, ← e]
    congr 1
    omega
  have h1 : M * X1 + M ≤ M * d := by
    have := Nat.mul_le_mul_left M (show X1 + 1 ≤ d by omega)
    rw [Nat.mul_add] at this; omega
  have hMd : M * d ≤ B * B - 1 := hM1
  have hMd2 : B * B - d ≤ M * d := by omega
  have hq1 : M * X1 + X0 < B * B := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ht']; exact Nat.div_lt_of_lt_mul hq1
  · have hBt : B * t1 ≤ M * X1 + X0 := by
      rw [ht']; have := Nat.div_mul_le_self (M * X1 + X0) B; rw [Nat.mul_comm]; exact this
    have h2 : d * (B * t1) ≤ d * (M * X1 + X0) := Nat.mul_le_mul_left d hBt
    have h3 : (M * d) * X1 ≤ (B * B - 1) * X1 := Nat.mul_le_mul_right X1 hMd
    have h3' : (B * B - 1) * X1 ≤ (B * B) * X1 := Nat.mul_le_mul_right X1 (by omega)
    have h4 : d * X0 ≤ B * X0 := Nat.mul_le_mul_right X0 (by omega)
    have e1 : d * (M * X1 + X0) = (M * d) * X1 + d * X0 := by grind
    have e2 : d * (B * t1) = B * (d * t1) := by grind
    have e3 : B * (X1 * B + X0) = (B * B) * X1 + B * X0 := by grind
    have : B * (d * t1) ≤ B * (X1 * B + X0) := by omega
    exact Nat.le_of_mul_le_mul_left this hB
  · have hBt : M * X1 + X0 < B * t1 + B := by
      rw [ht']
      have h1 := Nat.div_add_mod (M * X1 + X0) B
      have h2 := Nat.mod_lt (M * X1 + X0) hB
      omega
    have h2 : d * (M * X1 + X0) < d * (B * t1 + B) := Nat.mul_lt_mul_of_pos_left hBt hd0
    have e1 : d * (M * X1 + X0) = (M * d) * X1 + d * X0 := by grind
    have e2 : d * (B * t1 + B) = B * (d * t1) + B * d := by grind
    have h3 : (B * B - d) * X1 ≤ (M * d) * X1 := Nat.mul_le_mul_right X1 hMd2
    have h3' : (B * B - d) * X1 + d * X1 = (B * B) * X1 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by have := Nat.mul_le_mul_right B (show d ≤ B by omega); omega)]
    have h5 : d * X1 + d * X0 + d ≤ d * d + d * B := by
      have := Nat.mul_le_mul_left d (show X1 + 1 ≤ d by omega)
      have := Nat.mul_le_mul_left d (show X0 + 1 ≤ B by omega)
      rw [Nat.mul_add] at *; omega
    have h6 : d * d ≤ d * B := Nat.mul_le_mul_left d (by omega)
    have e3 : B * (X1 * B + X0) = (B * B) * X1 + B * X0 := by grind
    have e4 : B * (d * t1 + B + d) = B * (d * t1) + B * B + B * d := by grind
    have h7 : d * B = B * d := Nat.mul_comm _ _
    have : B * (X1 * B + X0) < B * (d * t1 + B + d) := by
      -- B*X = BB X1 + B X0 ;  d*B*t1 + ... see arith.go:314-327
      have hD : B * X0 + (d * B + B) ≤ d * X0 + B * B + d := by
        obtain ⟨e, he⟩ : ∃ e, B = d + e := ⟨B - d, by omega⟩
        have h := Nat.mul_le_mul_left e (show X0 + 1 ≤ B by omega)
        subst he
        grind
      have hA : d * X1 + d ≤ d * d := by
        have := Nat.mul_le_mul_left d (show X1 + 1 ≤ d by omega); rw [Nat.mul_add] at this; omega
      omega
    exact Nat.lt_of_mul_lt_mul_left this

/-- (arith.go:332-343) the two corrections.  `R = X - d*t1 < B + d`; the machine's `r0 = R % B`, `r1 != 0 <-> B <= R`. -/
theorem corrections (d X t1 : Nat) (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (h1 : d * t1 ≤ X) (h2 : X < d * t1 + 2 ^ 64 + d) :
    let R := X - d * t1
    let q1 := if 2 ^ 64 ≤ R then t1 + 1 else t1
    let r1 := if 2 ^ 64 ≤ R then (R % 2 ^ 64 + 2 ^ 64 - d) % 2 ^ 64 else R % 2 ^ 64
    (if d ≤ r1 then q1 + 1 else q1) = X / d ∧
      (if d ≤ r1 then (r1 + 2 ^ 64 - d) % 2 ^ 64 else r1) = X % d := by
  intro R q1 r1
  have hd0 : 0 < d := by omega
  have hq : ∀ q r, d * q + r = X → r < d → q = X / d ∧ r = X % d := by
    intro q r h hr
    have e1 : X / d = q := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm]; omega
      · rw [Nat.mul_comm]; have : d * q + d = d * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
        omega
    refine ⟨e1.symm, ?_⟩
    have := Nat.div_add_mod X d
    rw [e1] at this; omega
  have hR : R = X - d * t1 := rfl
  by_cases hc : 2 ^ 64 ≤ R
  · have hq1 : q1 = t1 + 1 := if_pos hc
    have hr1 : r1 = R - d := by
      show (if 2 ^ 64 ≤ R then _ else _) = _
      rw [if_pos hc]; omega
    have hlt : r1 < 2 ^ 64 := by omega
    by_cases hd' : d ≤ r1
    · simp only [if_pos hd', hq1]
      have := hq (t1 + 1 + 1) ((r1 + 2 ^ 64 - d) % 2 ^ 64) ?_ ?_
      · exact this
      · have e : d * (t1 + 1 + 1) = d * t1 + d + d := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega
      · omega
    · simp only [if_neg hd', hq1]
      refine hq (t1 + 1) r1 ?_ (by omega)
      have e : d * (t1 + 1) = d * t1 + d := by rw [Nat.mul_add, Nat.mul_one]
      omega
  · have hq1 : q1 = t1 := if_neg hc
    have hr1 : r1 = R := by
      show (if 2 ^ 64 ≤ R then _ else _) = _
      rw [if_neg hc]; omega
    by_cases hd' : d ≤ r1
    · simp only [if_pos hd', hq1]
      refine hq (t1 + 1) ((r1 + 2 ^ 64 - d) % 2 ^ 64) ?_ ?_
      · have e : d * (t1 + 1) = d * t1 + d := by rw [Nat.mul_add, Nat.mul_one]
        omega
      · omega
    · simp only [if_neg hd', hq1]
      refine hq t1 r1 ?_ (by omega)
      omega

/-- (arith.go:273-278) normalisation: `y << s` with `2^63 <= y*2^s < 2^64`, the dividend `X = x1*B + x0` with `x1 < y`
becomes `X1*B + X0 = X * 2^s`, with `X1 = x1*2^s + x0/2^(64-s)` and `X0 = x0*2^s mod 2^64`; then
`X*2^s / (y*2^s) = X / y` and `(X*2^s) % (y*2^s) = (X % y) * 2^s`. -/
theorem normalise (x1 x0 y s : Nat) (hy : 0 < y) (hs : s ≤ 63) (hys : y * 2 ^ s < 2 ^ 64) (hx1 : x1 < y)
    (hx0 : x0 < 2 ^ 64) :
    let X1 := x1 * 2 ^ s + x0 / 2 ^ (64 - s)
    let X0 := x0 * 2 ^ s % 2 ^ 64
    X1 * 2 ^ 64 + X0 = (x1 * 2 ^ 64 + x0) * 2 ^ s ∧ X1 < y * 2 ^ s ∧ X0 < 2 ^ 64 := by
  intro X1 X0
  have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have hq : 0 < 2 ^ (64 - s) := Nat.two_pow_pos _
  -- x0 * 2^s = (x0 / 2^(64-s)) * 2^64 + (x0 % 2^(64-s)) * 2^s
  have hx0d : x0 = 2 ^ (64 - s) * (x0 / 2 ^ (64 - s)) + x0 % 2 ^ (64 - s) := (Nat.div_add_mod _ _).symm
  have hlow : x0 % 2 ^ (64 - s) < 2 ^ (64 - s) := Nat.mod_lt _ hq
  have hX0 : X0 = (x0 % 2 ^ (64 - s)) * 2 ^ s := by
    show x0 * 2 ^ s % 2 ^ 64 = _
    rw [e64, Nat.mul_comm (2 ^ s), Nat.mul_mod_mul_right, Nat.mul_comm]
  have hqlt : x0 / 2 ^ (64 - s) < 2 ^ s := by
    apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, ← e64]; exact hx0
  have hX0lt : X0 < 2 ^ 64 := by
    rw [hX0, e64, Nat.mul_comm (2 ^ s)]
    exact Nat.mul_lt_mul_of_pos_right hlow hp
  refine ⟨?_, ?_, hX0lt⟩
  · show (x1 * 2 ^ s + x0 / 2 ^ (64 - s)) * 2 ^ 64 + X0 = _
    rw [hX0]
    generalize 2 ^ s = P at *
    generalize 2 ^ (64 - s) = Q at *
    generalize x0 / Q = a at *
    generalize x0 % Q = b at *
    rw [e64]
    rw [hx0d]
    grind
  · show x1 * 2 ^ s + x0 / 2 ^ (64 - s) < y * 2 ^ s
    have := Nat.mul_le_mul_right (2 ^ s) (show x1 + 1 ≤ y by omega)
    rw [Nat.add_mul] at this; omega

end FvModexp.AsmDiv
