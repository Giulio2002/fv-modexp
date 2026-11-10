import Janus

/-!
# Nat lemmas for the word-division proofs (shared)

`or_split`/`or_hi`/`or_hi_comm` and `clz_norm` are adapted from fv-uint256 `Fv256/Proofs/Common/Util.lean`
(`or_split`, `or_hi`, `or_hi_comm`) and `Fv256/Proofs/Arm64/RecipNat.lean` (`clz_norm`).
-/

namespace FvModexp.AsmDiv

theorem or_split (k a b c d : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * c) ||| (b + 2 ^ k * d) = (a ||| b) + 2 ^ k * (c ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hab : a ||| b < 2 ^ k := Nat.or_lt_two_pow ha hb
  rw [Nat.testBit_or, Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a ||| b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases h : i < k
  · simp [h, Nat.testBit_or]
  · simp [h, Nat.testBit_or]

theorem or_hi (a c k : Nat) (ha : a < 2 ^ k) : a ||| (c * 2 ^ k) = a + c * 2 ^ k := by
  have := or_split k a 0 0 c ha (Nat.two_pow_pos k)
  simpa [Nat.mul_comm] using this

theorem or_hi_comm (a c k : Nat) (ha : a < 2 ^ k) : c * 2 ^ k ||| a = a + c * 2 ^ k := by
  rw [Nat.or_comm]; exact or_hi a c k ha

open Janus.Arm64 in
theorem clz_norm : ∀ (n x : Nat), x < 2 ^ n → x ≠ 0 →
    2 ^ (n - 1) ≤ x * 2 ^ (clzNat n x) ∧ x * 2 ^ (clzNat n x) < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x hx h0; omega
  | succ n ih =>
    intro x hx h0
    have hc : clzNat (n + 1) x = if x.testBit n = true then 0 else 1 + clzNat n x := rfl
    rw [hc]
    by_cases hb : x.testBit n = true
    · rw [if_pos hb, Nat.pow_zero, Nat.mul_one]
      have h2 : 2 ^ n ≤ x := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · have := Nat.testBit_lt_two_pow hlt (i := n)
          rw [this] at hb
          exact absurd hb (by decide)
        · exact hge
      rw [Nat.add_sub_cancel]
      omega
    · rw [if_neg hb]
      have hxn : x < 2 ^ n := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · exact hlt
        · exfalso
          have h1 : x / 2 ^ n = 1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
              omega
          apply hb
          rw [Nat.testBit_eq_decide_div_mod_eq, h1]
          decide
      obtain ⟨h1, h2⟩ := ih x hxn h0
      have e : 2 ^ (1 + clzNat n x) = 2 * 2 ^ clzNat n x := by
        rw [Nat.add_comm, Nat.pow_succ]; omega
      rw [e]
      have e2 : x * (2 * 2 ^ clzNat n x) = 2 * (x * 2 ^ clzNat n x) := by
        rw [Nat.mul_left_comm]
      rw [e2]
      cases n with
      | zero => omega
      | succ k =>
        rw [Nat.add_sub_cancel]
        rw [Nat.add_sub_cancel] at h1
        have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
        have h4 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
        omega

theorem clz_norm64 (x : Nat) (hx0 : x ≠ 0) (hx : x < 2 ^ 64) :
    Janus.Arm64.clzNat 64 x ≤ 63 ∧ 2 ^ 63 ≤ x * 2 ^ Janus.Arm64.clzNat 64 x ∧
      x * 2 ^ Janus.Arm64.clzNat 64 x < 2 ^ 64 := by
  obtain ⟨h1, h2⟩ := clz_norm 64 x hx hx0
  refine ⟨?_, h1, h2⟩
  rcases Nat.lt_or_ge (Janus.Arm64.clzNat 64 x) 64 with hh | hh
  · omega
  · exfalso
    have h64 : 2 ^ 64 ≤ 2 ^ Janus.Arm64.clzNat 64 x := Nat.pow_le_pow_right (by omega) hh
    have : 2 ^ 64 ≤ x * 2 ^ Janus.Arm64.clzNat 64 x := by
      calc 2 ^ 64 = 1 * 2 ^ 64 := (Nat.one_mul _).symm
        _ ≤ x * 2 ^ Janus.Arm64.clzNat 64 x := Nat.mul_le_mul (Nat.pos_of_ne_zero hx0) h64
    omega

end FvModexp.AsmDiv
