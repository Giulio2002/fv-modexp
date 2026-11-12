import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# The arithmetic of `karatsubaSqr` (go-bigmodexpfix natmul.go:257-312), ISA independent (agent divmc)

With `E = 2^(64·n2)`, `X = x0 + E·x1` (`x0 = x[:n2]`, `x1 = x[n2:]`):
* `z1 = -(x0 - x1)²` (the square of `tx = x0 - x1`, sign set), then `z1 + x0² + x1² = 2·x0·x1` (`ks_z1`);
* `z = x0² + E²·x1²` after the two inner squares (clear, then `z[0:2n2]`, `z[2n2:]`);
* `addTo(z[n2:], z1)` adds `2·x0·x1` at limb `n2` modulo the length of `z[n2:]`, which does not wrap since
  `X² < E·F` (`ks_final`).
-/

namespace FvModexp

theorem ks_sq_expand (x0 x1 E : Nat) :
    (x0 + E * x1) * (x0 + E * x1) = x0 * x0 + E * (2 * x0 * x1) + E * E * (x1 * x1) := by
  have e : (x0 + E * x1) * (x0 + E * x1) = x0 * x0 + x0 * (E * x1) + (E * x1) * x0 + (E * x1) * (E * x1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have h1 : x0 * (E * x1) = E * (x0 * x1) := by ac_rfl
  have h2 : (E * x1) * x0 = E * (x0 * x1) := by ac_rfl
  have h3 : (E * x1) * (E * x1) = E * E * (x1 * x1) := by ac_rfl
  have h4 : E * (2 * x0 * x1) = 2 * (E * (x0 * x1)) := by ac_rfl
  omega

/-- the high part after `addTo` does not wrap -/
theorem ks_final {lo hi w x0 x1 E F : Nat}
    (hEF : (x0 + E * x1) * (x0 + E * x1) < E * F)
    (h0 : lo + E * hi = x0 * x0 + E * E * (x1 * x1)) (hw : w = 2 * x0 * x1) :
    lo + E * ((hi + w) % F) = (x0 + E * x1) * (x0 + E * x1) := by
  have hx := ks_sq_expand x0 x1 E
  have hs : lo + E * (hi + w) = (x0 + E * x1) * (x0 + E * x1) := by
    rw [Nat.mul_add, ← Nat.add_assoc, h0, hx, hw]; omega
  have hlt : hi + w < F := by
    have : E * (hi + w) < E * F := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  rw [Nat.mod_eq_of_lt hlt, hs]

/-- the Int value of `z1` after `z1 = -(x0-x1)²; z1 += x0²; z1 += x1²` -/
theorem ks_z1 (x0 x1 : Nat) :
    -((((x0 : Int) - x1).natAbs * ((x0 : Int) - x1).natAbs : Nat) : Int) + ((x0 * x0 : Nat) : Int) +
      ((x1 * x1 : Nat) : Int) = ((2 * x0 * x1 : Nat) : Int) := by
  have h : ((((x0 : Int) - x1).natAbs * ((x0 : Int) - x1).natAbs : Nat) : Int) = ((x0 : Int) - x1) * ((x0 : Int) - x1) := by
    rw [Int.natCast_mul, Int.natAbs_mul_self']
  rw [h]
  push_cast
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (x1 : Int) (x0 : Int), Int.mul_assoc 2]
  omega

/-- a canonical-sign Int whose value is a natural number: sign clear and `abs = v` -/
theorem int_nonneg_abs {neg : Nat} {a v : Nat}
    (hv : (if neg = 0 then (a : Int) else -(a : Int)) = (v : Int)) (hn : neg ≤ 1) (hcan : neg = 1 → 0 < a) :
    a = v := by
  by_cases h : neg = 0
  · rw [if_pos h] at hv; exact_mod_cast hv
  · rw [if_neg h] at hv
    have : 0 < a := hcan (by omega)
    omega

end FvModexp
