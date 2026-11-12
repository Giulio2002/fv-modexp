import FvModexp.Proofs.Arm64.Nat.KMulB

set_option autoImplicit false

/-!
# `karatsuba` (arm64): small value lemmas for the products written into the cleared `z`
-/

open Janus Janus.Arm64

namespace FvModexp.Arm64.NatMul

/-- a region that was zero, of which only the first `need` limbs were (exactly) written with `v` -/
theorem fill_val {m0 m1 : Memory} {p need N v : Nat} (hN : need ≤ N) (h0 : natVal m0 p N = 0)
    (hw : natVal m1 p need = v ∨ (v = 0 ∧ natVal m1 p need = natVal m0 p need))
    (hkeep : natVal m1 (p + 8 * need) (N - need) = natVal m0 (p + 8 * need) (N - need)) : natVal m1 p N = v := by
  have e0 := natVal_add m0 p need (N - need)
  have e1 := natVal_add m1 p need (N - need)
  rw [show need + (N - need) = N by omega] at e0 e1
  have hpos : 0 < 2 ^ (64 * need) := Nat.pow_pos (by decide)
  have hz1 : natVal m0 p need = 0 := by
    rcases Nat.eq_zero_or_pos (natVal m0 p need) with h | h
    · exact h
    · omega
  have hz2 : natVal m0 (p + 8 * need) (N - need) = 0 := by
    rcases Nat.eq_zero_or_pos (natVal m0 (p + 8 * need) (N - need)) with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ (64 * need)) h; omega
  rw [e1, hkeep, hz2, Nat.mul_zero, Nat.add_zero]
  rcases hw with hw | ⟨hv, hw⟩
  · exact hw
  · rw [hw, hz1, hv]

/-- a canonical-sign header whose signed value is a natural number has sign `0` and that value -/
theorem sgn_nonneg {m : Memory} {p ng l : Nat} {v : Nat} (hv : sgnV ng (natVal m p l) = (v : Int)) (hng : ng ≤ 1)
    (hcan : ng = 1 → 0 < l) (hn : NatNorm m p l) : ng = 0 ∧ natVal m p l = v := by
  unfold sgnV at hv
  by_cases h : ng = 0
  · rw [if_pos h] at hv; exact ⟨h, by exact_mod_cast hv⟩
  · rw [if_neg h] at hv
    have := SubMod2N.natVal_lower m p l hn (hcan (by omega))
    have : 0 < 2 ^ (64 * (l - 1)) := Nat.pow_pos (by decide)
    omega

end FvModexp.Arm64.NatMul
