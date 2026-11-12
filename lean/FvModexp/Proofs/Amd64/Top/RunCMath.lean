import FvModexp.Proofs.Amd64.Top.RunLMath
import FvModexp.Proofs.Common.RunMath

/-! # `Run` (amd64): arithmetic facts for the compute part (`mod.BitLen()`, `base.BitLen() == 1` for operands of up to 128
limbs; amd64 `nat.bitLen` = `(n - 1) << 6 + BSR(top) + 1`). Pure; the ISA-independent lemmas are copies of the arm64
`RunCMath` ones. -/

open Janus Janus.Arm64

namespace FvModexp.Amd64.Run

/-- `n - 1` of a limb count `1 ≤ n ≤ 2^62` is non-negative (`TESTQ; JL` falls through). -/
theorem msb_sub_one_le64 (n : Nat) (h1 : 1 ≤ n) (h : n ≤ 2 ^ 62) : (BitVec.ofNat 64 n - 1#64).msb = false := by
  have e : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega
  rw [e, BitVec.msb_eq_decide]; simp; omega

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

/-- A smear `x >>> k ||| y` is non-zero when `y` is. -/
theorem bv_or_ne_right_shr {x y : BitVec 64} {k : Nat} (h : y.toNat ≠ 0) : (x >>> k ||| y).toNat ≠ 0 := by
  rw [BitVec.toNat_or]; have := @Nat.right_le_or (x >>> k).toNat y.toNat; omega

/-- The value amd64 `nat.bitLen` computes for `n ≤ 2^20` limbs and a smeared top limb `Y ≠ 0`. -/
theorem blr_val64' (Y n : Nat) (hY0 : Y ≠ 0) (hY : Y < 2 ^ 64) (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 20) :
    64 * (n - 1) < ((BitVec.ofNat 64 n - 1#64) <<< 6 + BitVec.ofNat 64 (63 - clzNat 64 Y + 1)).toNat ∧
      ((BitVec.ofNat 64 n - 1#64) <<< 6 + BitVec.ofNat 64 (63 - clzNat 64 Y + 1)).toNat ≤ 64 * n := by
  have hc := clzNat_lt 64 Y (Nat.pos_of_ne_zero hY0) hY
  generalize clzNat 64 Y = c at *
  have hs : ((BitVec.ofNat 64 n - 1#64) <<< 6).toNat = 64 * (n - 1) := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub]; simp [Nat.shiftLeft_eq]
    rw [show (18446744073709551615 + n) * 64 = 64 * (n - 1) + 18446744073709551616 * 64 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 63 - c + 1) (by omega)]
  omega

/-- The amd64 bit length is `1` exactly when the top limb `x` is `1` and `n = 1` (`X` = its smear). -/
theorem blr_one64 (x X n : Nat) (hx0 : 0 < x) (hxX : x ≤ X) (hX1 : x = 1 → X = 1) (hX : X < 2 ^ 64)
    (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 20) :
    ((BitVec.ofNat 64 n - 1#64) <<< 6 + BitVec.ofNat 64 (63 - clzNat 64 X + 1)).toNat = 1 ↔ (n = 1 ∧ x = 1) := by
  have hb := blr_val64' X n (by omega) hX h1 hn
  constructor
  · intro h
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨rfl, ?_⟩
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · omega
    · have := clzNat_le_sub 64 1 X (by omega) hX
      have hc := clzNat_le 64 X
      have h64 : ((BitVec.ofNat 64 1 - 1#64) <<< 6 + BitVec.ofNat 64 (63 - clzNat 64 X + 1)).toNat =
          63 - clzNat 64 X + 1 := by
        generalize clzNat 64 X = c at *
        rw [BitVec.toNat_add]; simp; omega
      omega
  · rintro ⟨rfl, rfl⟩
    rw [hX1 rfl]; decide

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run

open Janus Janus.Arm64

/-- `n` padded call-data bytes are below `256^n`. -/
theorem padBE_lt (m : Memory) (p len start n : Nat) : padBE m p len start n < 256 ^ n := by
  induction n with
  | zero => simp [padBE]
  | succ n ih =>
    have hb : padByte m p len (start + n) < 256 := by
      unfold padByte; split
      · exact (m.bytes _).isLt
      · omega
    simp only [padBE, Nat.pow_succ]
    have : padBE m p len start n * 256 + 256 ≤ 256 ^ n * 256 := by
      have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt ih); rw [Nat.succ_mul] at this; exact this
    omega

/-- A normalised nat of `n` limbs is at least `2^(64 (n - 1))` (`n ≥ 1`). -/
theorem natVal_ge_norm (m : Memory) (p n : Nat) (hn : NatNorm m p n) (h1 : 1 ≤ n) :
    2 ^ (64 * (n - 1)) ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have ht : m.readLE (p + 8 * k) 8 ≠ 0 := by
    rcases hn with h | h
    · omega
    · simpa using h
  rw [natVal_succ, show k + 1 - 1 = k by omega]
  have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * m.readLE (p + 8 * k) 8 := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ht)
  omega

/-- A normalised nat below `2^(8 h)` has at most `⌈h / 8⌉` limbs. -/
theorem len_le_of_lt (m : Memory) (p n h : Nat) (hn : NatNorm m p n) (hv : natVal m p n < 2 ^ (8 * h)) :
    n ≤ (h + 7) / 8 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · omega
  · have := natVal_ge_norm m p n hn h0
    have h2 : 2 ^ (64 * (n - 1)) < 2 ^ (8 * h) := Nat.lt_of_le_of_lt this hv
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

/-- A normalised nat is below a normalised nat of more limbs... used as: a value below `y` has at most `len y` limbs. -/
theorem len_le_of_lt_norm (m m' : Memory) (p n p' n' : Nat) (hn : NatNorm m p n)
    (hv : natVal m p n < natVal m' p' n') : n ≤ n' := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · omega
  · have := natVal_ge_norm m p n hn h0
    have := natVal_lt m' p' n'
    have h2 : 2 ^ (64 * (n - 1)) < 2 ^ (64 * n') := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

/-- A minimal big-endian byte string (no leading zero byte) below `256^h` has at most `h` bytes. -/
theorem beLen_le (m : Memory) (q n h : Nat) (hmin : n = 0 ∨ (m.bytes q).toNat ≠ 0) (hv : beVal m q n < 256 ^ h) :
    n ≤ h := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · omega
  · have hb : (m.bytes q).toNat ≠ 0 := hmin.resolve_left (by omega)
    have hs := beVal_add m q 1 (n - 1)
    rw [show 1 + (n - 1) = n by omega] at hs
    have h1 : beVal m q 1 = (m.bytes q).toNat := by simp [beVal]
    rw [h1] at hs
    have : 256 ^ (n - 1) ≤ (m.bytes q).toNat * 256 ^ (n - 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hb)
    have h2 : 256 ^ (n - 1) < 256 ^ h := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

end FvModexp.Amd64.Run
