import FvModexp.Proofs.Common.AsmDivNat
import FvModexp.Proofs.Common.Conv

/-!
# Lemmas for `addVW` / `subVW` (go-bigmodexpfix arith.go:103, :157): slice-pointer masks of `copy(z[j:], x[j:])`
and the value of a `memmove` copy.
-/

namespace FvModexp.Asm

open Janus Janus.Arm64

theorem rot63_mod2 (v : BitVec 64) : (v.rotateRight 63).toNat % 2 = v.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_rotateRight]
  simp only [show 63 % 64 = 63 from rfl, show 64 - 63 = 1 from rfl]
  have hv := v.isLt
  have e : v.toNat <<< 1 % 2 ^ 64 = (v.toNat % 2 ^ 63) * 2 ^ 1 := by rw [Nat.shiftLeft_eq]; omega
  have hA : v.toNat >>> 63 < 2 ^ 1 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [e, Nat.or_comm, FvModexp.AsmDiv.or_hi_comm _ _ _ hA, Nat.shiftRight_eq_div_pow]
  omega

/-- arm64 `SUB; NEG; ASR #63; AND #8` of a slice capacity: `8` when `1 < cap`, else `0` (`x[1:]`'s pointer) -/
theorem mask8 (c : BitVec 64) (hc : c.toNat < 2 ^ 63) (h1 : 1 ≤ c.toNat) :
    (((if (0#64 - (c - 1#64)).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 18446744073709551614 |||
      ((0#64 - (c - 1#64)).rotateRight 63).toNat % 2) &&& 8) = if 1 < c.toNat then 8 else 0 := by
  rw [rot63_mod2]
  have hv : (0#64 - (c - 1#64)).toNat = (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hb : (0#64 - (c - 1#64)).getLsbD 63 = decide (2 ^ 63 ≤ (0#64 - (c - 1#64)).toNat) :=
    BitVec.getLsbD_last _
  rw [hb, hv]
  by_cases h : 1 < c.toNat
  · have e1 : 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by omega
    have e2 : (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 / 2 ^ 63 = 1 := by omega
    simp only [e1, e2, decide_true, if_true, h]
    decide
  · have e1 : ¬ 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by omega
    have e2 : (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 / 2 ^ 63 = 0 := by omega
    simp only [e1, e2, decide_false, h]
    decide

/-- the bytes a `memmove` copied, read as a little-endian value -/
theorem readLE_of_copied {m0 m : Memory} {dst src n : Nat} (h : Janus.Contracts.Mem.Copied m0 m dst src n) :
    m.readLE dst n = m0.readLE src n := by
  induction n generalizing dst src with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [Memory.readLE_succ, Memory.readLE_succ, h0, ih (fun i hi => by
      have := h (i + 1) (by omega); rw [show dst + (i + 1) = dst + 1 + i by omega,
        show src + (i + 1) = src + 1 + i by omega] at this; exact this)]

end FvModexp.Asm

namespace FvModexp.Asm
open Janus Janus.Arm64

/-- `ASR #63`: all ones or zero by the sign bit -/
theorem sshr63 (x : BitVec 64) : x.sshiftRight 63 = if 2 ^ 63 ≤ x.toNat then BitVec.allOnes 64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_sshiftRight]
  have hm := BitVec.msb_eq_decide x
  simp only [show (64 - 1) = 63 from rfl] at hm
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [h, ite_true, BitVec.getLsbD_allOnes, hk, decide_true]
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.add_zero, show 63 < 64 from by decide, ite_true]
      rw [BitVec.getLsbD_last]; simp [h]
    · have : ¬ 63 + k < 64 := by omega
      simp only [this, ite_false]
      rw [hm]; simp [h, hk]
  · simp only [h, ite_false, BitVec.getLsbD_zero]
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.add_zero, show 63 < 64 from by decide, ite_true]
      rw [BitVec.getLsbD_last]; simp [h]
    · have : ¬ 63 + k < 64 := by omega
      simp only [this, ite_false]
      rw [hm]; simp [h]

/-- arm64 `SUB; SUB; NEG; AND X9, X7 ASR #63; LSL #3` (the loop's `copy(z[i+1:], x[i+1:])` pointer offset) -/
theorem maskB (c : BitVec 64) (i : Nat) (hc : c.toNat < 2 ^ 63) (hi : i + 1 ≤ c.toNat) (hi8 : i < 2 ^ 60) :
    ((BitVec.ofNat 64 i + 1#64 &&& (0#64 - (c - BitVec.ofNat 64 (i + 1))).sshiftRight 63) <<< 3).toNat =
      if i + 1 < c.toNat then 8 * (i + 1) else 0 := by
  rw [sshr63]
  have hv : (0#64 - (c - BitVec.ofNat 64 (i + 1))).toNat = (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hv]
  by_cases h : i + 1 < c.toNat
  · have e : 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by omega
    simp only [e, ite_true, h, BitVec.and_allOnes, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  · have e : ¬ 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by omega
    simp only [e, ite_false, h, BitVec.and_zero, BitVec.zero_shiftLeft, BitVec.toNat_ofNat]

end FvModexp.Asm

namespace FvModexp.Asm
open Janus Janus.Arm64

/-- `CMN Xn, #1`: the zero flag says `Xn = 2^64 - 1` -/
theorem cmn1_z (v : Nat) (hv : v < 2 ^ 64) :
    (addWithCarry (BitVec.ofNat 64 v) (1#64) false).snd.z = decide (v = 2 ^ 64 - 1) := by
  simp only [addWithCarry, BitVec.toNat_ofNat, Bool.toNat_false, Nat.mod_eq_of_lt hv]
  by_cases h : v = 2 ^ 64 - 1
  · subst h; decide
  · have : BitVec.ofNat 64 (v + 1 % 2 ^ 64 + 0) ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    simp [this, h]

theorem readLE_limb_split (m : Memory) (p i : Nat) :
    m.readLE p (8 * (i + 1)) = m.readLE p (8 * i) + 2 ^ (64 * i) * m.readLE (p + i * 8) 8 := by
  rw [show 8 * (i + 1) = 8 * i + 8 by omega, Memory.readLE_add, show p + 8 * i = p + i * 8 by omega,
    show (256 : Nat) ^ (8 * i) = 2 ^ (64 * i) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]

theorem readLE_write_top (m : Memory) (p i v : Nat) :
    (m.writeLE (p + i * 8) 8 v).readLE p (8 * (i + 1)) = m.readLE p (8 * i) + 2 ^ (64 * i) * (v % 2 ^ 64) := by
  rw [readLE_limb_split, Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

/-- the carry passes limb `i = 2^64 - 1` (`z[i] = 0`) -/
theorem v_ones (m m0 : Memory) (zp xp i y : Nat)
    (hval : m.readLE zp (8 * i) + 2 ^ (64 * i) = m0.readLE xp (8 * i) + y)
    (hx : m0.readLE (xp + i * 8) 8 = 2 ^ 64 - 1) :
    (m.writeLE (zp + i * 8) 8 0).readLE zp (8 * (i + 1)) + 2 ^ (64 * (i + 1)) = m0.readLE xp (8 * (i + 1)) + y := by
  rw [readLE_write_top, readLE_limb_split m0, hx, show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
  have : 2 ^ (64 * i) * (2 ^ 64 - 1) + 2 ^ (64 * i) = 2 ^ (64 * i) * 2 ^ 64 := by
    rw [Nat.mul_sub_one]; have := Nat.two_pow_pos (64 * i)
    have : 2 ^ (64 * i) ≤ 2 ^ (64 * i) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega
  simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  omega

/-- the carry stops at limb `i < 2^64 - 1` (`z[i] = x[i] + 1`) -/
theorem v_inc (m m0 : Memory) (zp xp i y : Nat)
    (hval : m.readLE zp (8 * i) + 2 ^ (64 * i) = m0.readLE xp (8 * i) + y)
    (hx : m0.readLE (xp + i * 8) 8 ≠ 2 ^ 64 - 1) :
    (m.writeLE (zp + i * 8) 8 (m0.readLE (xp + i * 8) 8 + 1)).readLE zp (8 * (i + 1)) =
      m0.readLE xp (8 * (i + 1)) + y := by
  have hl := Memory.readLE_lt m0 (xp + i * 8) 8
  rw [readLE_write_top, readLE_limb_split m0, Nat.mod_eq_of_lt (by simp at hl; omega), Nat.mul_add]
  omega

end FvModexp.Asm

namespace FvModexp.Asm
open Janus Janus.Arm64

/-- the BitVec form of `mask8` (as the executor leaves the pointer of `x[1:]`) -/
theorem mask8B (c : BitVec 64) (hc : c.toNat < 2 ^ 63) (h1 : 1 ≤ c.toNat) :
    (((if (0#64 - (c - 1#64)).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
        (0#64 - (c - 1#64)).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) &&& 8#64).toNat =
      if 1 < c.toNat then 8 else 0 := by
  rw [← mask8 c hc h1]
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have e : ((0#64 - (c - 1#64)).rotateRight 63).toNat &&& 18446744073709551615 =
      ((0#64 - (c - 1#64)).rotateRight 63).toNat := by
    have := ((0#64 - (c - 1#64)).rotateRight 63).isLt
    rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]
  rw [e, Nat.and_one_is_mod]

/-- limb 0: the `ADDS; ADC XZR, XZR; CBZ` carry test -/
theorem carry0 (a : Nat) (ha : a < 2 ^ 64) (y : BitVec 64) :
    ((addWithCarry (0#64) (0#64) (addWithCarry (BitVec.ofNat 64 a) y false).snd.c).fst.toNat = 0) =
      (a + y.toNat < 2 ^ 64) := by
  rw [addWithCarry_fst_toNat, addWithCarry_c64]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Bool.toNat_false, Nat.add_zero]
  by_cases h : 2 ^ 64 ≤ a + y.toNat
  · simp only [h, decide_true, Bool.toNat_true]; apply propext
    constructor <;> intro hh <;> first | omega | (simp at hh) | (exfalso; omega)
  · simp only [h, decide_false, Bool.toNat_false]; apply propext
    constructor <;> intro hh <;> first | omega | simp

end FvModexp.Asm

namespace FvModexp.Asm
open Janus Janus.Arm64

/-- the borrow passes limb `i = 0` (`z[i] = 2^64 - 1`) -/
theorem v_zero (m m0 : Memory) (zp xp i y : Nat)
    (hval : m.readLE zp (8 * i) + y = m0.readLE xp (8 * i) + 2 ^ (64 * i))
    (hx : m0.readLE (xp + i * 8) 8 = 0) :
    (m.writeLE (zp + i * 8) 8 (2 ^ 64 - 1)).readLE zp (8 * (i + 1)) + y = m0.readLE xp (8 * (i + 1)) + 2 ^ (64 * (i + 1)) := by
  rw [readLE_write_top, readLE_limb_split m0, hx, show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
  have : 2 ^ (64 * i) * (2 ^ 64 - 1) + 2 ^ (64 * i) = 2 ^ (64 * i) * 2 ^ 64 := by
    rw [Nat.mul_sub_one]; have := Nat.two_pow_pos (64 * i)
    have : 2 ^ (64 * i) ≤ 2 ^ (64 * i) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 64 - 1 < 2 ^ 64), Nat.mul_zero, Nat.add_zero]
  omega

/-- the borrow stops at limb `i`, `x[i] ≠ 0` (`z[i] = x[i] - 1`) -/
theorem v_dec (m m0 : Memory) (zp xp i y : Nat)
    (hval : m.readLE zp (8 * i) + y = m0.readLE xp (8 * i) + 2 ^ (64 * i))
    (hx : m0.readLE (xp + i * 8) 8 ≠ 0) :
    (m.writeLE (zp + i * 8) 8 (m0.readLE (xp + i * 8) 8 - 1)).readLE zp (8 * (i + 1)) + y =
      m0.readLE xp (8 * (i + 1)) := by
  have hl := Memory.readLE_lt m0 (xp + i * 8) 8
  rw [readLE_write_top, readLE_limb_split m0, Nat.mod_eq_of_lt (by simp at hl; omega), Nat.mul_sub_one]
  have : 2 ^ (64 * i) ≤ 2 ^ (64 * i) * m0.readLE (xp + i * 8) 8 := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- limb 0: the `SUBS; NGC XZR; NEG; CBZ` borrow test, in the executor's form -/
theorem borrow0 (a : Nat) (ha : a < 2 ^ 64) (y : BitVec 64) :
    ((18446744073709551616 - (addWithCarry (0#64) (18446744073709551615#64)
        (addSub (BitVec.ofNat 64 a) y true).snd.c).fst.toNat) % 18446744073709551616 = 0) = (y.toNat ≤ a) := by
  have hc : (addSub (BitVec.ofNat 64 a) y true).snd.c = decide (y.toNat ≤ a) := by
    simp only [addSub, ite_true]
    rw [addWithCarry_c64]
    simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Bool.toNat_true]
    have := y.isLt
    by_cases h : y.toNat ≤ a
    · simp only [h, decide_true]; apply decide_eq_true; omega
    · simp only [h, decide_false]; apply decide_eq_false; omega
  rw [hc, addWithCarry_fst_toNat]
  by_cases h : y.toNat ≤ a
  · simp only [h, decide_true, Bool.toNat_true]; decide
  · simp only [h, decide_false, Bool.toNat_false, BitVec.toNat_ofNat]
    simp

end FvModexp.Asm

namespace FvModexp.Asm
open Janus

/-- amd64 `SUB; LEA -1; NEG; SAR $63; AND (i+1)<<3` (the loop's `copy(z[i+1:], x[i+1:])` pointer offset) -/
theorem maskB64 (c : BitVec 64) (i : Nat) (hc : c.toNat < 2 ^ 63) (hi : i + 1 ≤ c.toNat) (hi8 : i < 2 ^ 60) :
    ((0#64 - (c - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) <<< 3).toNat =
      if i + 1 < c.toNat then 8 * (i + 1) else 0 := by
  rw [sshr63]
  have hv : (0#64 - (c - BitVec.ofNat 64 (i + 1))).toNat = (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hv]
  by_cases h : i + 1 < c.toNat
  · have e : 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by omega
    simp only [e, ite_true, h, BitVec.allOnes_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · have e : ¬ 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - (i + 1))) % 2 ^ 64 := by omega
    simp only [e, ite_false, h, BitVec.zero_and, BitVec.toNat_ofNat]

end FvModexp.Asm

namespace FvModexp.Asm
open Janus

/-- amd64 `LEA -1; NEG; SAR $63; AND $8` (32-bit `AND`, zero-extended) of a slice capacity: `x[1:]`'s pointer offset -/
theorem mask8_64 (c : BitVec 64) (hc : c.toNat < 2 ^ 63) (h1 : 1 ≤ c.toNat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - (c - 1#64)).sshiftRight 63) &&& 8#32)).toNat =
      if 1 < c.toNat then 8 else 0 := by
  rw [sshr63]
  have hv : (0#64 - (c - 1#64)).toNat = (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hv]
  by_cases h : 1 < c.toNat
  · have e : 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by omega
    simp only [e, ite_true, h]; decide
  · have e : ¬ 2 ^ 63 ≤ (2 ^ 64 - (c.toNat - 1)) % 2 ^ 64 := by omega
    simp only [e, ite_false, h]; decide

end FvModexp.Asm
