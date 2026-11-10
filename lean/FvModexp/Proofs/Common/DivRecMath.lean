import FvModexp.Proofs.Common.DivRecAux
/-!
# Pure Nat lemmas for one wide-digit step of `divRecursiveStep` (natdiv.go:750-892)

The "Good Guess Guarantee" of the comment in natdiv.go (lines 166-300): with `x = x1·S + x0`, `y = y1·S + y0`, `x0, y0 < S`,
`T ≤ 2·y1`, `x < y·T`, the truncated quotient `q̂ = ⌊x1/y1⌋` satisfies `q ≤ q̂ ≤ q + 2` for `q = ⌊x/y⌋`.
-/
namespace FvModexp.Mdl

theorem gg_lower (x x1 x0 y y1 y0 S : Nat) (hx : x = x1 * S + x0) (hx0 : x0 < S) (hy : y = y1 * S + y0) (hy1 : 0 < y1) :
    x / y ≤ x1 / y1 := by
  have hyp : 0 < y := by
    have : 0 < y1 * S := Nat.mul_pos hy1 (by omega)
    omega
  refine Nat.le_of_not_gt ?_
  intro hlt
  have h1 : (x1 / y1 + 1) * y ≤ x := (Nat.le_div_iff_mul_le hyp).1 hlt
  have hd := Nat.div_add_mod x1 y1
  have hm := Nat.mod_lt x1 hy1
  have h2 : x1 + 1 ≤ (x1 / y1 + 1) * y1 := by
    rw [Nat.add_mul, Nat.one_mul]; rw [Nat.mul_comm] at hd; omega
  have h3 : (x1 / y1 + 1) * (y1 * S) ≤ (x1 / y1 + 1) * y := Nat.mul_le_mul_left _ (by omega)
  have h4 : (x1 + 1) * S ≤ (x1 / y1 + 1) * y1 * S := Nat.mul_le_mul_right _ h2
  rw [Nat.mul_assoc] at h4
  have h5 : (x1 + 1) * S = x1 * S + S := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem gg_upper (x x1 x0 y y1 y0 S T : Nat) (hx : x = x1 * S + x0) (hy : y = y1 * S + y0) (hy0 : y0 < S)
    (hT : T ≤ 2 * y1) (hxy : x < y * T) (hy1 : 0 < y1) :
    x1 / y1 ≤ x / y + 2 := by
  have hSp : 0 < S := by omega
  have hyp : 0 < y := by
    have : 0 < y1 * S := Nat.mul_pos hy1 hSp
    omega
  refine Nat.le_of_not_gt ?_
  intro hlt
  have hq3 : (x / y + 3) ≤ x1 / y1 := by omega
  have h1 : (x / y + 3) * y1 ≤ x1 := (Nat.le_div_iff_mul_le hy1).1 hq3
  have h2 : (x / y + 3) * y1 * S ≤ x1 * S := Nat.mul_le_mul_right _ h1
  have hd := Nat.div_add_mod x y
  have hm := Nat.mod_lt x hyp
  have h3 : x < y * (x / y + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have h4 : y < (y1 + 1) * S := by rw [Nat.add_mul, Nat.one_mul]; omega
  have h5 : y * (x / y + 1) ≤ (y1 + 1) * S * (x / y + 1) := Nat.mul_le_mul_right _ (by omega)
  have h6 : (x / y + 3) * y1 * S < (x / y + 1) * (y1 + 1) * S := by
    have : (x / y + 3) * y1 * S ≤ x := by omega
    have e : (y1 + 1) * S * (x / y + 1) = (x / y + 1) * (y1 + 1) * S := by
      rw [Nat.mul_comm ((y1 + 1) * S), Nat.mul_assoc]
    omega
  have h7 : (x / y + 3) * y1 < (x / y + 1) * (y1 + 1) := Nat.lt_of_mul_lt_mul_right h6
  have h8 : 2 * y1 < x / y + 1 := by
    generalize x / y = q at *
    have e1 : (q + 3) * y1 = q * y1 + 3 * y1 := by rw [Nat.add_mul]
    have e2 : (q + 1) * (y1 + 1) = q * y1 + q + y1 + 1 := by rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega
  have h9 : x / y < T := by
    have : x / y * y ≤ x := Nat.div_mul_le_self x y
    have h10 : x / y * y < T * y := by rw [Nat.mul_comm T]; omega
    exact Nat.lt_of_mul_lt_mul_right h10
  omega

/-- `Q < q_k` iff `Y_k < q_k·v0` where `X = q_k·(v1·S) + Y_k` and `v = v1·S + v0` (the `qhatv.cmp(uu.norm()) > 0` test). -/
theorem cmp_iff (X v v1S v0 qk Yk : Nat) (hvp : 0 < v) (hv : v = v1S + v0) (hX : X = qk * v1S + Yk) :
    X / v < qk ↔ Yk < qk * v0 := by
  rw [Nat.div_lt_iff_lt_mul hvp]
  have : qk * v = qk * v1S + qk * v0 := by rw [hv, Nat.mul_add]
  omega

end FvModexp.Mdl
