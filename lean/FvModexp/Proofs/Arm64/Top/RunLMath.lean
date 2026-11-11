import FvModexp.Proofs.Common.Conv

/-! # `Run` (arm64): arithmetic facts for the length checks (`CLZ` bounds, header values by limb count) -/

open Janus Janus.Arm64

namespace FvModexp.Arm64.Run

theorem clzNat_le (n x : Nat) : clzNat n x ≤ n := by
  induction n with
  | zero => simp [clzNat]
  | succ n ih => unfold clzNat; split <;> omega

theorem clzNat_lt (n x : Nat) (h0 : 0 < x) (hx : x < 2 ^ n) : clzNat n x < n := by
  induction n with
  | zero => simp at hx; omega
  | succ n ih =>
    unfold clzNat
    split
    · omega
    · rename_i hb
      have : x < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rcases Nat.lt_or_eq_of_le hi with h | h
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h))
        · subst h; simpa using hb
      have := ih this; omega

/-- A normalised nat of at least two limbs is at least `2^64`. -/
theorem natVal_ge_of_norm (m : Memory) (p n : Nat) (hn : NatNorm m p n) (h2 : 2 ≤ n) : 2 ^ 64 ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases hn with h | h
  · omega
  · rw [natVal_succ]
    simp only [Nat.add_sub_cancel] at h
    have h1 : 1 ≤ m.readLE (p + 8 * k) 8 := Nat.pos_of_ne_zero h
    have h3 : 2 ^ 64 ≤ 2 ^ (64 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    have := Nat.mul_le_mul h3 h1
    omega

theorem natVal_one (m : Memory) (p : Nat) : natVal m p 1 = m.readLE p 8 := rfl

end FvModexp.Arm64.Run
