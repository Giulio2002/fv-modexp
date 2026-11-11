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

namespace FvModexp.Arm64.Run

/-- `n - 1` of a limb count `1 ≤ n ≤ 4` is non-negative (the `TBNZ $63` of `nat.bitLen` falls through). -/
theorem msb_sub_one_small (n : Nat) (h1 : 1 ≤ n) (h4 : n ≤ 4) :
    ((BitVec.ofNat 64 n - 1#64).getLsbD 63 == true) = false := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl <;> decide

theorem or_pos_left' {a b : Nat} (h : 0 < a) : 0 < a ||| b :=
  Nat.lt_of_lt_of_le h (Nat.left_le_or)

/-- The value `nat.bitLen` computes for a top limb `X ≠ 0` (after the bit smear) and `n` limbs. -/
theorem blr_val (X n : Nat) (hX0 : 0 < X) (hX : X < 2 ^ 64) (h1 : 1 ≤ n) (h4 : n ≤ 4) :
    64 * (n - 1) < (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 n - 1#64) <<< 6).toNat ∧
      (64#64 - BitVec.ofNat 64 (clzNat 64 X) + (BitVec.ofNat 64 n - 1#64) <<< 6).toNat ≤ 64 * n := by
  have hc := clzNat_lt 64 X hX0 hX
  generalize clzNat 64 X = c at *
  have h64 : (64#64 - BitVec.ofNat 64 c).toNat = 64 - c := by
    rw [BitVec.toNat_sub]; simp; omega
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl <;>
  · rw [BitVec.toNat_add, h64]
    simp
    omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

theorem toNat_ofNat_readLE_pos (m : Memory) (a : Nat) (h : m.readLE a 8 ≠ 0) :
    0 < (BitVec.ofNat 64 (m.readLE a 8)).toNat := by
  have := Memory.readLE_lt m a 8
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using this)]; omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

/-- What Run's length check needs of one length header with value `v` after `BitLen` (`bl`) and `Uint64` (`u`): the bit
length is small, it exceeds 64 exactly when `v ≥ 2^64`, and otherwise `u` is `v`. -/
def LenRegs (v : Nat) (bl u : BitVec 64) : Prop :=
  bl.toNat ≤ 256 ∧ (64 < bl.toNat ↔ 2 ^ 64 ≤ v) ∧ (bl.toNat ≤ 64 → u.toNat = v)

theorem lenRegs_z {v : Nat} {bl u : BitVec 64} (hv : v = 0) (hb : 0#64 = bl) (hu : 0#64 = u) : LenRegs v bl u := by
  subst hb hu hv; refine ⟨by decide, ?_, fun _ => rfl⟩; simp

theorem lenRegs_nz {m : Memory} {pt n v : Nat} {bl u : BitVec 64} (hv : v = natVal m pt n) (hnorm : NatNorm m pt n)
    (h1 : 1 ≤ n) (h4 : n ≤ 4) (hk : 64 * (n - 1) < bl.toNat ∧ bl.toNat ≤ 64 * n)
    (hu : BitVec.ofNat 64 (m.readLE pt 8) = u) : LenRegs v bl u := by
  refine ⟨by omega, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rw [hv]; exact natVal_ge_of_norm m pt n hnorm (by omega)
  · refine Nat.lt_of_not_le fun hc => ?_
    have hn1 : n = 1 := by omega
    subst hn1
    have := natVal_lt m pt 1
    omega
  · have hn1 : n = 1 := by omega
    subst hn1 hu
    rw [hv, natVal_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Memory.readLE_lt m pt 8; simpa using this)]

end FvModexp.Arm64.Run
