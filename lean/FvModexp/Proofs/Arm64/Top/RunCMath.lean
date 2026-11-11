import FvModexp.Proofs.Arm64.Top.RunLMath

/-! # `Run` (arm64): arithmetic facts for the compute part (`mod.BitLen()`, `base.BitLen() == 1` for operands of up to 128
limbs) -/

open Janus Janus.Arm64

namespace FvModexp.Arm64.Run

/-- `n - 1` of a limb count `1 ≤ n ≤ 2^62` is non-negative (the `TBNZ $63` of `nat.bitLen` falls through). -/
theorem msb_sub_one_le (n : Nat) (h1 : 1 ≤ n) (h : n ≤ 2 ^ 62) :
    ((BitVec.ofNat 64 n - 1#64).getLsbD 63 == true) = false := by
  have e : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega
  rw [e, BitVec.getLsbD_ofNat]
  have : (n - 1).testBit 63 = false := Nat.testBit_lt_two_pow (by omega)
  simp [this]

/-- `CLZ` of a value of at least `2^k` is at most `n - 1 - k`. -/
theorem clzNat_le_sub (n k x : Nat) (hk : 2 ^ k ≤ x) (hx : x < 2 ^ n) : clzNat n x + k + 1 ≤ n := by
  induction n with
  | zero => have := Nat.one_le_two_pow (n := k); simp at hx; omega
  | succ n ih =>
    unfold clzNat
    split
    · have : k < n + 1 := (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt hk hx)
      omega
    · rename_i hb
      have hx' : x < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rcases Nat.lt_or_eq_of_le hi with h | h
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h))
        · subst h; simpa using hb
      have := ih hx'; omega

/-- The value `nat.bitLen` computes for a top limb whose smear is `X ≠ 0`, and `n ≤ 2^20` limbs. -/
theorem blr_val' (X n : Nat) (hX0 : 0 < X) (hX : X < 2 ^ 64) (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 20) :
    64 * (n - 1) < (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 n - 1#64) <<< 6).toNat ∧
      (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 n - 1#64) <<< 6).toNat ≤ 64 * n := by
  have hc := clzNat_lt 64 X hX0 hX
  generalize clzNat 64 X = c at *
  have h64 : (64#64 - BitVec.ofNat 64 c).toNat = 64 - c := by
    rw [BitVec.toNat_sub]; simp; omega
  have hs : ((BitVec.ofNat 64 n - 1#64) <<< 6).toNat = 64 * (n - 1) := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub]; simp [Nat.shiftLeft_eq]
    rw [show (18446744073709551615 + n) * 64 = 64 * (n - 1) + 18446744073709551616 * 64 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, h64, hs]
  omega

/-- The value `nat.bitLen` computes is `1` exactly when the top limb is `1` (`n = 1`). -/
theorem blr_one (x X n : Nat) (hx0 : 0 < x) (hxX : x ≤ X) (hX1 : x = 1 → X = 1) (hX : X < 2 ^ 64)
    (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 20) :
    (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 n - 1#64) <<< 6).toNat = 1 ↔ (n = 1 ∧ x = 1) := by
  have hb := blr_val' X n (by omega) hX h1 hn
  constructor
  · intro h
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨rfl, ?_⟩
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · omega
    · have := clzNat_le_sub 64 1 X (by omega) hX
      have h64 : (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 1 - 1#64) <<< 6).toNat = 64 - clzNat 64 X := by
        have hc := clzNat_le 64 X
        generalize clzNat 64 X = c at *
        rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
      omega
  · rintro ⟨rfl, rfl⟩
    rw [hX1 rfl]; decide

end FvModexp.Arm64.Run
