import FvModexp.Proofs.Common.Limbs
import FvModexp.Proofs.Common.Div64Math
/-!
# Word-level operations of `math/big` (arith.go) and `math/bits`

Models over `Nat` with explicit `2^64` arithmetic (uint64 wrap-around is spelled `% 2^64`), mirroring the Go source line by line.
Panics (divide by zero, quotient overflow) are *not* modelled: each theorem carries the Go precondition under which the call does not
panic.

* `mulWW`                 arith.go:43-46   (`bits.Mul` = `Mul64` : (x*y)/2^64, (x*y)%2^64)
* `mulAddWWW`             arith.go:49-54   (`mulAddWWW_g`)
* `nlz`                   arith.go:58-60   (`bits.LeadingZeros64`)
* `div64`                 go1.26 math/bits/bits.go:518-568 (`bits.Div64`, software version; used by arm64 machine code, intrinsified DIVQ on amd64)
* `divWW`                 arith.go:273-330 (`divWW`: Moller-Granlund style 2-by-1 with approximate reciprocal)
* `reciprocalWord`        arith.go:333-339
-/
namespace FvModexp.Mdl

/-- `bits.Mul64`: (hi, lo). -/
def mulWW (x y : Nat) : Nat × Nat := (x * y / 2 ^ 64, x * y % 2 ^ 64)

/-- `bits.Add64(x, y, c)` = (sum, carry-out). -/
def addc (x y c : Nat) : Nat × Nat := ((x + y + c) % 2 ^ 64, (x + y + c) / 2 ^ 64)

/-- `bits.Sub64(x, y, b)` = (diff, borrow-out). -/
def subb (x y b : Nat) : Nat × Nat := ((x + 2 ^ 64 - y - b) % 2 ^ 64, if x < y + b then 1 else 0)

/-- arith.go:49 `mulAddWWW_g`: z1<<64 + z0 = x*y + c. -/
def mulAddWWW (x y c : Nat) : Nat × Nat :=
  let (hi, lo) := mulWW x y
  let (lo, cc) := addc lo c 0
  ((hi + cc) % 2 ^ 64, lo)

/-- `bits.LeadingZeros64`. -/
def nlz (y : Nat) : Nat := if y = 0 then 64 else 63 - Nat.log2 y

theorem nlz_spec (y : Nat) (h0 : 0 < y) (h : y < 2 ^ 64) :
    nlz y ≤ 63 ∧ y * 2 ^ nlz y < 2 ^ 64 ∧ 2 ^ 63 ≤ y * 2 ^ nlz y := by
  have hy : y ≠ 0 := by omega
  have hk : y.log2 < 64 := (Nat.log2_lt hy).2 h
  have h1 : 2 ^ y.log2 ≤ y := (Nat.le_log2 hy).1 (Nat.le_refl _)
  have h2 : y < 2 ^ (y.log2 + 1) := Nat.lt_log2_self
  have e : nlz y = 63 - y.log2 := by unfold nlz; simp [hy]
  rw [e]
  refine ⟨by omega, ?_, ?_⟩
  · have : y * 2 ^ (63 - y.log2) < 2 ^ (y.log2 + 1) * 2 ^ (63 - y.log2) :=
      Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at this
    have : y.log2 + 1 + (63 - y.log2) = 64 := by omega
    simp_all
  · have : 2 ^ y.log2 * 2 ^ (63 - y.log2) ≤ y * 2 ^ (63 - y.log2) := Nat.mul_le_mul_right _ h1
    rw [← Nat.pow_add] at this
    have : y.log2 + (63 - y.log2) = 63 := by omega
    simp_all

theorem mulWW_spec (x y : Nat) : (mulWW x y).1 * 2 ^ 64 + (mulWW x y).2 = x * y := by
  unfold mulWW; simp only []; have := Nat.div_add_mod (x * y) (2 ^ 64); grind

theorem mulAddWWW_spec (x y c : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hc : c < 2 ^ 64) :
    (mulAddWWW x y c).1 * 2 ^ 64 + (mulAddWWW x y c).2 = x * y + c ∧
    (mulAddWWW x y c).1 < 2 ^ 64 ∧ (mulAddWWW x y c).2 < 2 ^ 64 := by
  unfold mulAddWWW mulWW addc
  simp only []
  have h1 := Nat.div_add_mod (x * y) (2 ^ 64)
  have hp : x * y < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  have h2 : x * y / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hp
  have h3 : x * y % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  have hp2 : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : x * y / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have : x * y < (2 ^ 64 - 1) * 2 ^ 64 := by
      have e : (2 ^ 64 - 1) * (2 ^ 64 - 1) + 1 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
        simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul]; omega
      omega
    have := Nat.div_lt_of_lt_mul this
    omega
  generalize x * y / 2 ^ 64 = hi at *
  generalize x * y % 2 ^ 64 = lo at *
  simp only [Nat.add_zero]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## bits.Div64 (software), go1.26 -/

/-- The correction loop of `Div64` (`for q >= two32 || q*yn0 > two32*rhat+un1 { q--; rhat += yn1; if rhat >= two32 { break } }`).
Total because the loop body is only entered when `q > 0`. -/
def d64loop (yn1 yn0 un1 q rhat : Nat) : Nat × Nat :=
  -- `0 < q` is implied by the loop condition (for q = 0 both disjuncts are false); it is stated for termination.
  if h : 0 < q ∧ (2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un1 < q * yn0) then
    if 2 ^ 32 ≤ rhat + yn1 then (q - 1, rhat + yn1) else d64loop yn1 yn0 un1 (q - 1) (rhat + yn1)
  else (q, rhat)
termination_by q
decreasing_by exact Nat.sub_lt h.1 Nat.one_pos

/-- `bits.Div64(hi, lo, y)` (quo, rem), the software algorithm of go1.26 math/bits/bits.go:518. -/
def div64 (hi lo y : Nat) : Nat × Nat :=
  if hi = 0 then (lo / y, lo % y) else
  let s := nlz y
  let y := y * 2 ^ s % 2 ^ 64
  let yn1 := y / 2 ^ 32
  let yn0 := y % 2 ^ 32
  let un32 := (hi * 2 ^ s % 2 ^ 64) ||| (lo / 2 ^ (64 - s))
  let un10 := lo * 2 ^ s % 2 ^ 64
  let un1 := un10 / 2 ^ 32
  let un0 := un10 % 2 ^ 32
  let q1 := un32 / yn1
  let rhat := un32 - q1 * yn1
  let q1 := (d64loop yn1 yn0 un1 q1 rhat).1
  let un21 := (un32 * 2 ^ 32 + un1 + 2 ^ 64 - q1 * y % 2 ^ 64) % 2 ^ 64
  let q0 := un21 / yn1
  let rhat := un21 - q0 * yn1
  let q0 := (d64loop yn1 yn0 un0 q0 rhat).1
  (q1 * 2 ^ 32 + q0, ((un21 * 2 ^ 32 + un0 + 2 ^ 64 - q0 * y % 2 ^ 64) % 2 ^ 64) / 2 ^ s)

/-- The loop returns the exact digit. -/
theorem d64loop_spec (yn1 yn0 un1 A : Nat) (hyn1 : 2 ^ 31 ≤ yn1) (hyn1B : yn1 < 2 ^ 32) (hyn0 : yn0 < 2 ^ 32) (hun1 : un1 < 2 ^ 32)
    (hA : A < yn1 * 2 ^ 32 + yn0) :
    ∀ (q rhat : Nat), q * yn1 + rhat = A → (A * 2 ^ 32 + un1) / (yn1 * 2 ^ 32 + yn0) ≤ q → q ≤ 2 ^ 32 + 1 →
      (d64loop yn1 yn0 un1 q rhat).1 = (A * 2 ^ 32 + un1) / (yn1 * 2 ^ 32 + yn0) := by
  generalize hT : (A * 2 ^ 32 + un1) / (yn1 * 2 ^ 32 + yn0) = T
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
  intro rhat hI hge hq
  have hy : 0 < yn1 * 2 ^ 32 + yn0 := by
    clear hT; omega
  rw [d64loop.eq_1]
  by_cases hc : 2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un1 < q * yn0
  · have hgt := D64.step_gt (2 ^ 32) yn1 yn0 A un1 q rhat hun1 hA hI hc
    rw [hT] at hgt
    have hq0 : 0 < q := by clear hT; omega
    have hc' : 0 < q ∧ (2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un1 < q * yn0) := ⟨hq0, hc⟩
    simp only [hc', dite_true]
    by_cases hr : 2 ^ 32 ≤ rhat + yn1
    · simp only [hr, ite_true]
      rw [← hT]
      refine D64.exit_break (2 ^ 32) yn1 yn0 A un1 (q - 1) (rhat + yn1) ?_ (by rw [hT]; clear hT; omega) hr (by clear hT; omega) hyn0 hy
      have : (q - 1) * yn1 + (rhat + yn1) = q * yn1 + rhat := by
        cases q with
        | zero => omega
        | succ q => simp [Nat.succ_mul]; omega
      clear hT; omega
    · simp only [hr, ite_false]
      refine ih (q - 1) (by clear hT; omega) (rhat + yn1) ?_ (by clear hT; omega) (by clear hT; omega)
      have : (q - 1) * yn1 + (rhat + yn1) = q * yn1 + rhat := by
        cases q with
        | zero => omega
        | succ q => simp [Nat.succ_mul]; omega
      clear hT; omega
  · have hc' : ¬ (0 < q ∧ (2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un1 < q * yn0)) := fun h => hc h.2
    simp only [hc', dite_false]
    rw [not_or, Nat.not_lt, Nat.not_le] at hc
    exact hT ▸ (D64.exit_eq (2 ^ 32) yn1 yn0 A un1 q rhat hI (hT ▸ hge) hc.2 hy)


theorem wrap_sub (N p : Nat) (hp : p ≤ N) (hN : N - p < 2 ^ 64) : (N + 2 ^ 64 - p % 2 ^ 64) % 2 ^ 64 = N - p := by
  omega

/-- One digit step of `Div64`: setup facts shared by both digits. -/
theorem d64_digit (yn1 yn0 un1 A : Nat) (hyn1 : 2 ^ 31 ≤ yn1) (hyn1B : yn1 < 2 ^ 32) (hyn0 : yn0 < 2 ^ 32)
    (hun1 : un1 < 2 ^ 32) (hA : A < yn1 * 2 ^ 32 + yn0) :
    (d64loop yn1 yn0 un1 (A / yn1) (A - A / yn1 * yn1)).1 = (A * 2 ^ 32 + un1) / (yn1 * 2 ^ 32 + yn0) := by
  have hy1 : 0 < yn1 := by omega
  have hI : A / yn1 * yn1 + (A - A / yn1 * yn1) = A := by
    have := Nat.div_mul_le_self A yn1; omega
  refine d64loop_spec yn1 yn0 un1 A hyn1 hyn1B hyn0 hun1 hA (A / yn1) _ hI ?_ ?_
  · exact D64.est_ge (2 ^ 32) yn1 yn0 A un1 (by omega) hun1 hy1
  · have := D64.init_bound (2 ^ 32) yn1 yn0 A (by omega) hyn0 hA
    exact this

theorem div64_spec (hi lo y : Nat) (hy : 0 < y) (hyB : y < 2 ^ 64) (hlo : lo < 2 ^ 64) (hhi : hi < y) :
    div64 hi lo y = ((hi * 2 ^ 64 + lo) / y, (hi * 2 ^ 64 + lo) % y) := by
  unfold div64
  by_cases h0 : hi = 0
  · subst h0; simp
  rw [if_neg h0]
  simp only []
  obtain ⟨hs63, hs1, hs2⟩ := nlz_spec y hy hyB
  generalize hs : nlz y = s at *
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have hy' : y * 2 ^ s % 2 ^ 64 = y * 2 ^ s := Nat.mod_eq_of_lt hs1
  rw [hy']
  -- shifted divisor and its halves
  obtain ⟨yn1, hyn1⟩ : ∃ v, v = y * 2 ^ s / 2 ^ 32 := ⟨_, rfl⟩
  obtain ⟨yn0, hyn0⟩ : ∃ v, v = y * 2 ^ s % 2 ^ 32 := ⟨_, rfl⟩
  rw [← hyn1, ← hyn0]
  have hdiv : y * 2 ^ s = yn1 * 2 ^ 32 + yn0 := by
    have := Nat.div_add_mod (y * 2 ^ s) (2 ^ 32); omega
  have hyn1a : 2 ^ 31 ≤ yn1 := by omega
  have hyn1b : yn1 < 2 ^ 32 := by omega
  have hyn0b : yn0 < 2 ^ 32 := by omega
  -- numerator pieces
  have hlo2 : lo / 2 ^ (64 - s) < 2 ^ s := by
    have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    apply Nat.div_lt_of_lt_mul
    rw [← e]; exact hlo
  have hhi2 : hi * 2 ^ s < 2 ^ 64 := by
    have : (hi + 1) * 2 ^ s ≤ y * 2 ^ s := Nat.mul_le_mul_right _ hhi
    rw [Nat.add_mul] at this; omega
  have hun32 : (hi * 2 ^ s % 2 ^ 64) ||| (lo / 2 ^ (64 - s)) = hi * 2 ^ s + lo / 2 ^ (64 - s) := by
    rw [Nat.mod_eq_of_lt hhi2, Nat.mul_comm hi (2 ^ s), ← Nat.two_pow_add_eq_or_of_lt hlo2 hi, Nat.mul_comm (2 ^ s) hi]
  rw [hun32]
  have hys : y * 2 ^ s < 2 ^ 64 := hs1
  have hU32lt : hi * 2 ^ s + lo / 2 ^ (64 - s) < yn1 * 2 ^ 32 + yn0 := by
    have : (hi + 1) * 2 ^ s ≤ y * 2 ^ s := Nat.mul_le_mul_right _ hhi
    rw [Nat.add_mul] at this; omega
  generalize hU32 : hi * 2 ^ s + lo / 2 ^ (64 - s) = U32 at *
  generalize hU10 : lo * 2 ^ s % 2 ^ 64 = U10 at *
  have hU10lt : U10 < 2 ^ 64 := by rw [← hU10]; exact Nat.mod_lt _ (by omega)
  have hun1 : U10 / 2 ^ 32 < 2 ^ 32 := by omega
  have hun0 : U10 % 2 ^ 32 < 2 ^ 32 := by omega
  rw [d64_digit yn1 yn0 (U10 / 2 ^ 32) U32 hyn1a hyn1b hyn0b hun1 hU32lt]
  rw [← hdiv]
  obtain ⟨Q1, hQ1'⟩ : ∃ Q, Q = (U32 * 2 ^ 32 + U10 / 2 ^ 32) / (y * 2 ^ s) := ⟨_, rfl⟩
  have hQ1 := hQ1'.symm
  simp only [← hQ1']
  have hD1 := Nat.div_add_mod (U32 * 2 ^ 32 + U10 / 2 ^ 32) (y * 2 ^ s)
  rw [hQ1] at hD1
  have hD1lt : (U32 * 2 ^ 32 + U10 / 2 ^ 32) % (y * 2 ^ s) < y * 2 ^ s := Nat.mod_lt _ (by omega)
  have hQ1m : y * 2 ^ s * Q1 = Q1 * (y * 2 ^ s) := Nat.mul_comm _ _
  have hR1 : (U32 * 2 ^ 32 + U10 / 2 ^ 32 + 2 ^ 64 - Q1 * (y * 2 ^ s) % 2 ^ 64) % 2 ^ 64
      = U32 * 2 ^ 32 + U10 / 2 ^ 32 - Q1 * (y * 2 ^ s) := by
    apply wrap_sub <;> (generalize Q1 * (y * 2 ^ s) = p at *; omega)
  rw [hR1]
  have hR1lt : U32 * 2 ^ 32 + U10 / 2 ^ 32 - Q1 * (y * 2 ^ s) < y * 2 ^ s := by
    generalize Q1 * (y * 2 ^ s) = p at *; omega
  obtain ⟨R1, hR1d'⟩ : ∃ R, R = U32 * 2 ^ 32 + U10 / 2 ^ 32 - Q1 * (y * 2 ^ s) := ⟨_, rfl⟩
  have hR1d := hR1d'.symm
  simp only [← hR1d'] at hR1lt ⊢
  rw [hdiv] at hR1lt
  rw [d64_digit yn1 yn0 (U10 % 2 ^ 32) R1 hyn1a hyn1b hyn0b hun0 hR1lt]
  rw [← hdiv]
  obtain ⟨Q0, hQ0'⟩ : ∃ Q, Q = (R1 * 2 ^ 32 + U10 % 2 ^ 32) / (y * 2 ^ s) := ⟨_, rfl⟩
  have hQ0 := hQ0'.symm
  simp only [← hQ0']
  have hD0 := Nat.div_add_mod (R1 * 2 ^ 32 + U10 % 2 ^ 32) (y * 2 ^ s)
  rw [hQ0] at hD0
  have hD0lt : (R1 * 2 ^ 32 + U10 % 2 ^ 32) % (y * 2 ^ s) < y * 2 ^ s := Nat.mod_lt _ (by omega)
  have hQ0m : y * 2 ^ s * Q0 = Q0 * (y * 2 ^ s) := Nat.mul_comm _ _
  have hR0 : (R1 * 2 ^ 32 + U10 % 2 ^ 32 + 2 ^ 64 - Q0 * (y * 2 ^ s) % 2 ^ 64) % 2 ^ 64
      = R1 * 2 ^ 32 + U10 % 2 ^ 32 - Q0 * (y * 2 ^ s) := by
    apply wrap_sub <;> (generalize Q0 * (y * 2 ^ s) = p at *; omega)
  rw [hR0]
  have := D64.assemble hi lo y s hy hys hhi (by omega) Q1 Q0 R1 (R1 * 2 ^ 32 + U10 % 2 ^ 32 - Q0 * (y * 2 ^ s))
    (U32 * 2 ^ 32 + U10 / 2 ^ 32) (R1 * 2 ^ 32 + U10 % 2 ^ 32) U32 U10 hU32.symm hU10.symm rfl hQ1.symm
    hR1d.symm rfl hQ0.symm rfl
  exact Prod.ext this.1 this.2

end FvModexp.Mdl
