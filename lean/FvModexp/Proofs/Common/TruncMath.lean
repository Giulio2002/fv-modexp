import FvModexp.Proofs.Common.SetBytesMath

/-!
# `nat.trunc`: the top-word mask (ISA-independent)

`z[w-1] &= 1<<(n%64) - 1` on `z[0:w] = x[0:w]` gives `X mod 2^n` (`n = 64 (w-1) + n % 64`, `0 < n % 64`).
-/

open Janus Janus.Arm64

namespace FvModexp.TruncMath

theorem mask_mod (lo t k r : Nat) (hlo : lo < 2 ^ (64 * k)) :
    (lo + 2 ^ (64 * k) * t) % 2 ^ (64 * k + r) = lo + 2 ^ (64 * k) * (t % 2 ^ r) := by
  have hR : 0 < 2 ^ r := Nat.two_pow_pos _
  have hm := Nat.mod_lt t hR
  have hlt : lo + 2 ^ (64 * k) * (t % 2 ^ r) < 2 ^ (64 * k) * 2 ^ r := by
    have h1 : 2 ^ (64 * k) * (t % 2 ^ r + 1) ≤ 2 ^ (64 * k) * 2 ^ r := Nat.mul_le_mul_left _ hm
    rw [Nat.mul_succ] at h1; omega
  have e : lo + 2 ^ (64 * k) * t = (lo + 2 ^ (64 * k) * (t % 2 ^ r)) + (2 ^ (64 * k) * 2 ^ r) * (t / 2 ^ r) := by
    conv => lhs; rw [← Nat.mod_add_div t (2 ^ r)]
    rw [Nat.mul_add, Nat.mul_assoc]; omega
  rw [Nat.pow_add, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem and_mask (t r : Nat) (hr1 : 1 ≤ r) (hr : r < 64) :
    t &&& (18446744073709551615 + 2 ^ r) % 18446744073709551616 = t % 2 ^ r := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr
  rw [show 18446744073709551615 + 2 ^ r = (2 ^ r - 1) + 18446744073709551616 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod t r

/-- the masked top word gives the value mod `2^(64 (w-1) + r)` -/
theorem mask_val (M : Memory) (p w r : Nat) (hw : 1 ≤ w) (hr1 : 1 ≤ r) (hr : r < 64) :
    natVal (M.writeLE (p + 8 * (w - 1)) 8
      (M.readLE (p + 8 * (w - 1)) 8 &&& (18446744073709551615 + 2 ^ r) % 18446744073709551616)) p w =
      natVal M p w % 2 ^ (64 * (w - 1) + r) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, and_mask _ _ hr1 hr,
    natVal_store_top _ _ _ _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by omega))),
    natVal_succ, mask_mod _ _ _ _ (natVal_lt _ _ _)]

/-- `LSR $6` as Janus spells it (rotate + masks) -/
theorem lit_bit (i : Nat) (hi : i < 64) (k : Nat) :
    (BitVec.ofNat 64 (2 ^ k - 1))[i] = decide (i < k) := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [hi]
theorem rot6 (v : BitVec 64) : v.rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 = v >>> 6 := by
  ext i hi
  have e1 := lit_bit i hi 58
  have e2 := lit_bit i hi 64
  simp only [show (2 : Nat) ^ 58 - 1 = 288230376151711743 from rfl, show (2 : Nat) ^ 64 - 1 = 18446744073709551615 from rfl] at e1 e2
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, e1, e2]
  by_cases h : i < 58
  · simp [h, hi, BitVec.getLsbD_eq_getElem, show 6 + i < 64 by omega]
  · simp [h, hi]; exact BitVec.getLsbD_of_ge _ _ (by omega)

end FvModexp.TruncMath
