/-
  ExpBase: word-level vocabulary and the generic "windowed exponentiation" loop shape shared by
  the Go routines of go-bigmodexpfix src/math/big/nat.go (module path
  github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab).

  Nat-level modelling convention (see /srv/fv-modexp-ops/NOTES-models.md):
  a Go `nat` ([]Word, W = 64) is modelled by the Nat it denotes; `len x` is `nlen x` (normalized
  length), word `x[i]` is `wd x i`.  nat.mul/sqr/div/rem/add/sub/cmp/lsh/rsh/trunc are the Nat
  operations `*`, `/`, `%`, `+`, `-`, compare, `* 2^s`, `/ 2^s`, `% 2^n` (their machine-level models are
  proved separately by agent "mathdiv").
-/
namespace FvModexp.Exp

/-- `2^_W`, `_W = 64` (nat.go: `_W = bits.UintSize`). -/
def B : Nat := 2 ^ 64

theorem B_eq : B = 18446744073709551616 := by unfold B; rfl

theorem B_def : B = 2 ^ 64 := by unfold B; rfl

theorem B_pos : 0 < B := by unfold B; exact Nat.two_pow_pos _

-- `B` is kept opaque so omega/grind do not expand the literal.
attribute [irreducible] B

/-- `len(x)` of a normalized nat. -/
def nlen (x : Nat) : Nat := if x = 0 then 0 else x.log2 / 64 + 1

/-- `x.bitLen()` (nat.go:355). -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else x.log2 + 1

/-- `x[i]` (0 beyond the length). -/
def wd (x i : Nat) : Nat := x / B ^ i % B

/-- `nat.trailingZeroBits` (nat.go:364). -/
def tz (x : Nat) : Nat :=
  if h : x = 0 then 0 else if x % 2 = 1 then 0 else 1 + tz (x / 2)
termination_by x
decreasing_by omega

/-- `nat.isPow2` (nat.go:379) on `x ≠ 0`: `i, true` iff `x == 2^i`. -/
def isPow2 (x : Nat) : Option Nat := if x = 2 ^ tz x then some (tz x) else none

/-- Euclid-free congruence on residues. -/
abbrev Cg (m a b : Nat) : Prop := a % m = b % m

theorem bitLen_lt {x : Nat} (hx : 0 < x) : x < 2 ^ bitLen x := by
  have hx' : x ≠ 0 := by omega
  simp only [bitLen, hx', ite_false]
  exact (Nat.log2_lt hx').1 (by omega)

theorem bitLen_ge {x : Nat} (hx : 0 < x) : 2 ^ (bitLen x - 1) ≤ x := by
  have hx' : x ≠ 0 := by omega
  simp only [bitLen, hx', ite_false]
  simpa using Nat.log2_self_le hx'

theorem bitLen_le_of_lt {x k : Nat} (h : x < 2 ^ k) : bitLen x ≤ k := by
  unfold bitLen; split
  · omega
  · rename_i hx
    have := (Nat.log2_lt hx).2 h; omega

theorem bitLen_pos {x : Nat} (hx : 0 < x) : 0 < bitLen x := by
  have hx' : x ≠ 0 := by omega
  simp only [bitLen, hx', ite_false]; omega

/-- `x < B^(nlen x)`. -/
theorem lt_B_nlen (x : Nat) : x < B ^ nlen x := by
  unfold nlen; split
  · simp [B]; omega
  · rename_i hx
    have h2 : x < 2 ^ (x.log2 + 1) := (Nat.log2_lt hx).1 (by omega)
    refine Nat.lt_of_lt_of_le h2 ?_
    unfold B; rw [← Nat.pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have := Nat.div_add_mod (x.log2) 64
    have := Nat.mod_lt (x.log2) (by omega : 64 > 0)
    -- x.log2 + 1 ≤ 64 * (x.log2/64 + 1)
    omega

theorem nlen_le_iff {x n : Nat} : nlen x ≤ n ↔ x < B ^ n := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (lt_B_nlen x) (Nat.pow_le_pow_right (by unfold B; exact Nat.two_pow_pos _) h)
  · intro h
    unfold nlen; split
    · omega
    · rename_i hx
      refine Nat.not_lt.mp (fun hc => ?_)
      have h1 : n ≤ x.log2 / 64 := by omega
      have h2 : B ^ n ≤ B ^ (x.log2 / 64) := Nat.pow_le_pow_right B_pos h1
      have h3 : B ^ (x.log2 / 64) ≤ x := by
        have := Nat.log2_self_le (n := x) hx
        unfold B; rw [← Nat.pow_mul]
        exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) this
      omega

/-- `f^[j] z` (sequence of `j` squarings in the unrolled loops). -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, z => z
  | j + 1, z => iter f j (f z)

theorem wd_lt (x i : Nat) : wd x i < B := Nat.mod_lt _ B_pos

end FvModexp.Exp
