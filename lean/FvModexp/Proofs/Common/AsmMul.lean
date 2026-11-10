import FvModexp.Proofs.Common.AsmLimbs

/-!
# Shared lemmas for the `mulAddVWW` / `addMulVVWW` assembly summaries (arm64 and amd64)

Nat-level carry-step lemmas (`mul_step`, `addmul_step`) and the arm64 `UMULH`/`MUL`/`ADDS`/`ADCS` limb arithmetic.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

/-- one block of `mulAddVWW`: `Z + P·C = X·m + a`, `r + W·C' = xb·m + C` gives
`Z + P·r + (P·W)·C' = (X + P·xb)·m + a` -/
theorem mul_step (P W Z C X a m xb r C' : Nat) (hs : Z + P * C = X * m + a)
    (ht : r + W * C' = xb * m + C) :
    Z + P * r + (P * W) * C' = (X + P * xb) * m + a := by
  have h1 : P * (r + W * C') = P * (xb * m + C) := by rw [ht]
  simp only [Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc] at h1 ⊢
  omega

/-- one block of `addMulVVWW`: `Z + P·C = X + Y·m + a`, `r + W·C' = xb + yb·m + C` gives
`Z + P·r + (P·W)·C' = (X + P·xb) + (Y + P·yb)·m + a` -/
theorem addmul_step (P W Z C X Y a m xb yb r C' : Nat) (hs : Z + P * C = X + Y * m + a)
    (ht : r + W * C' = xb + yb * m + C) :
    Z + P * r + (P * W) * C' = (X + P * xb) + (Y + P * yb) * m + a := by
  have h1 : P * (r + W * C') = P * (xb + yb * m + C) := by rw [ht]
  simp only [Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc] at h1 ⊢
  omega

theorem adc_eq (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).snd.c.toNat * 2 ^ 64 + (addWithCarry a b c).fst.toNat = a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  have hf : (addWithCarry a b c).fst.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
    simp [addWithCarry, BitVec.toNat_ofNat]
  rw [hf]
  simp only [addWithCarry, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 ≠ a.toNat + b.toNat + c.toNat := by omega
    simp only [ne_eq, this, not_false_eq_true, decide_true, Bool.toNat_true]; omega
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 = a.toNat + b.toNat + c.toNat := Nat.mod_eq_of_lt (by omega)
    simp only [ne_eq, this, not_true_eq_false, decide_false, Bool.toNat_false]; omega

theorem flag_le (c : Bool) : c.toNat ≤ 1 := by cases c <;> simp

/-- the low and high halves of `UMULH`/`MUL` of a loaded limb `a` by `m` -/
def ml (a : Nat) (m : BitVec 64) : BitVec 64 := BitVec.ofNat 64 a * m
def mh (a : Nat) (m : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 a) * BitVec.setWidth 128 m)

theorem lohi (a : Nat) (m : BitVec 64) (ha : a < 2 ^ 64) :
    (ml a m).toNat + 2 ^ 64 * (mh a m).toNat = a * m.toNat := by
  have h1 : (ml a m).toNat = (a * m.toNat) % 2 ^ 64 := by
    unfold ml; rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have h2 : (mh a m).toNat = a * m.toNat / 18446744073709551616 := by
    unfold mh; rw [Janus.Tactic.umulh_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [h1, h2]
  have := Nat.mod_add_div (a * m.toNat) (2 ^ 64)
  omega

theorem mh_lt (a : Nat) (m : BitVec 64) (ha : a < 2 ^ 64) : (mh a m).toNat + 1 < 2 ^ 64 := by
  have h := lohi a m ha
  have hm := m.isLt
  have hp : a * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by decide
  omega

/-- `ADC hi, zr` after `ADDS`: the new carry word is `hi + flag` -/
theorem carry_word (hi : BitVec 64) (f : Bool) (hh : hi.toNat + 1 < 2 ^ 64) :
    (addWithCarry hi 0#64 f).fst.toNat = hi.toNat + f.toNat := by
  have h := adc_eq hi 0#64 f
  have := flag_le f
  simp only [BitVec.toNat_ofNat] at h
  have := (addWithCarry hi 0#64 f).fst.isLt
  have h0 : (0#64).toNat = 0 := rfl
  omega

/-- the one-limb step of `mulAddVWW`: `x·m + c = r + 2^64·c'` -/
theorem mul1 (a : Nat) (m c : BitVec 64) (ha : a < 2 ^ 64) :
    ((ml a m).toNat + c.toNat) % 2 ^ 64 +
      2 ^ 64 * (addWithCarry (mh a m) 0#64 (addWithCarry (ml a m) c false).snd.c).fst.toNat =
    a * m.toNat + c.toNat := by
  rw [carry_word _ _ (mh_lt a m ha)]
  have h := adc_eq (ml a m) c false
  have h2 := lohi a m ha
  have hf : (addWithCarry (ml a m) c false).fst.toNat = ((ml a m).toNat + c.toNat) % 2 ^ 64 := by
    simp [addWithCarry, BitVec.toNat_ofNat]
  simp only [Bool.toNat_false] at h
  omega


def cf (l h : BitVec 64) (f : Bool) : Bool := (addWithCarry l h f).snd.c
def cr (l h : BitVec 64) (f : Bool) : BitVec 64 := (addWithCarry l h f).fst

set_option exponentiation.threshold 1024 in
theorem pow_i8 (i : Nat) : 2 ^ (64 * (i + 8)) = 2 ^ (64 * i) * 2 ^ 512 := by
  rw [Nat.mul_add, Nat.pow_add]

theorem lv_add8 (m : Memory) (p i : Nat) :
    lv m p (i + 8) = lv m p i + 2 ^ (64 * i) * (m.readLE (p + 8 * i) 8 + 2 ^ 64 * m.readLE (p + 8 * i + 8) 8 + 2 ^ 128 * m.readLE (p + 8 * i + 16) 8 + 2 ^ 192 * m.readLE (p + 8 * i + 24) 8 + 2 ^ 256 * m.readLE (p + 8 * i + 32) 8 + 2 ^ 320 * m.readLE (p + 8 * i + 40) 8 + 2 ^ 384 * m.readLE (p + 8 * i + 48) 8 + 2 ^ 448 * m.readLE (p + 8 * i + 56) 8) := by
  have e1 := lv_add4 m p i
  have e2 := lv_add4 m p (i + 4)
  rw [pow_i4] at e2
  rw [show p + 8 * (i + 4) = p + 8 * i + 32 by omega, show p + 8 * i + 32 + 8 = p + 8 * i + 40 by omega,
    show p + 8 * i + 32 + 16 = p + 8 * i + 48 by omega, show p + 8 * i + 32 + 24 = p + 8 * i + 56 by omega] at e2
  rw [show i + 4 + 4 = i + 8 from rfl] at e2
  rw [e2, e1]
  generalize 2 ^ (64 * i) = K at *
  have hc : ∀ c x : Nat, K * (c * x) = c * (K * x) := fun c x => Nat.mul_left_comm K c x
  simp only [Nat.mul_add, Nat.mul_assoc, hc]
  omega

theorem lv_write8 (m : Memory) (p i v0 v1 v2 v3 v4 v5 v6 v7 : Nat) :
    lv ((((((((m.writeLE (p + 8 * i) 8 v0).writeLE (p + 8 * i + 8) 8 v1).writeLE (p + 8 * i + 16) 8 v2).writeLE (p + 8 * i + 24) 8 v3).writeLE (p + 8 * i + 32) 8 v4).writeLE (p + 8 * i + 40) 8 v5).writeLE (p + 8 * i + 48) 8 v6).writeLE (p + 8 * i + 56) 8 v7) p (i + 8) =
      lv m p i + 2 ^ (64 * i) * (v0 % 2 ^ 64 + 2 ^ 64 * (v1 % 2 ^ 64) + 2 ^ 128 * (v2 % 2 ^ 64) + 2 ^ 192 * (v3 % 2 ^ 64) + 2 ^ 256 * (v4 % 2 ^ 64) + 2 ^ 320 * (v5 % 2 ^ 64) + 2 ^ 384 * (v6 % 2 ^ 64) + 2 ^ 448 * (v7 % 2 ^ 64)) := by
  have e1 := lv_write4 m p i v0 v1 v2 v3
  have e2 := lv_write4 ((((m.writeLE (p + 8 * i) 8 v0).writeLE (p + 8 * i + 8) 8 v1).writeLE (p + 8 * i + 16) 8 v2).writeLE
        (p + 8 * i + 24) 8 v3) p (i + 4) v4 v5 v6 v7
  rw [show p + 8 * (i + 4) = p + 8 * i + 32 by omega, show p + 8 * i + 32 + 8 = p + 8 * i + 40 by omega,
    show p + 8 * i + 32 + 16 = p + 8 * i + 48 by omega, show p + 8 * i + 32 + 24 = p + 8 * i + 56 by omega] at e2
  rw [e2, e1, pow_i4]
  generalize 2 ^ (64 * i) = K at *
  have hc : ∀ c x : Nat, K * (c * x) = c * (K * x) := fun c x => Nat.mul_left_comm K c x
  simp only [Nat.mul_add, Nat.mul_assoc, hc]
  omega

theorem frame_ext8 {m m' : Memory} {z i : Nat} (h : MemFrame m m' [(z, z + 8 * i)]) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) :
    MemFrame m ((((((((m'.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2).writeLE
      (z + 8 * i + 24) 8 v3).writeLE (z + 8 * i + 32) 8 v4).writeLE (z + 8 * i + 40) 8 v5).writeLE
      (z + 8 * i + 48) 8 v6).writeLE (z + 8 * i + 56) 8 v7) [(z, z + 8 * (i + 8))] := by
  have h4 := frame_ext4 h v0 v1 v2 v3
  have := frame_ext4 h4 v4 v5 v6 v7
  rw [show z + 8 * (i + 4) = z + 8 * i + 32 by omega, show z + 8 * i + 32 + 8 = z + 8 * i + 40 by omega,
    show z + 8 * i + 32 + 16 = z + 8 * i + 48 by omega, show z + 8 * i + 32 + 24 = z + 8 * i + 56 by omega,
    show z + 8 * (i + 4 + 4) = z + 8 * (i + 8) by omega] at this
  exact this


/-- the eight-limb block of the arm64 `mulAddVWW` loop (`UMULH`/`MUL`, `ADDS`, 7 × `ADCS`, `ADC ZR`):
`r_j` are the stored limbs, `c'` the new carry word -/
theorem mulblk8 (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (ha4 : a4 < 2 ^ 64) (ha5 : a5 < 2 ^ 64) (ha6 : a6 < 2 ^ 64) (ha7 : a7 < 2 ^ 64) (m c : BitVec 64)
    (r1 r2 r3 r4 r5 r6 r7 c' : BitVec 64) (f0 f1 f2 f3 f4 f5 f6 f7 : Bool)
    (hf0 : f0 = cf (ml a0 m) c false)
    (hr1 : r1 = cr (ml a1 m) (mh a0 m) f0) (hf1 : f1 = cf (ml a1 m) (mh a0 m) f0)
    (hr2 : r2 = cr (ml a2 m) (mh a1 m) f1) (hf2 : f2 = cf (ml a2 m) (mh a1 m) f1)
    (hr3 : r3 = cr (ml a3 m) (mh a2 m) f2) (hf3 : f3 = cf (ml a3 m) (mh a2 m) f2)
    (hr4 : r4 = cr (ml a4 m) (mh a3 m) f3) (hf4 : f4 = cf (ml a4 m) (mh a3 m) f3)
    (hr5 : r5 = cr (ml a5 m) (mh a4 m) f4) (hf5 : f5 = cf (ml a5 m) (mh a4 m) f4)
    (hr6 : r6 = cr (ml a6 m) (mh a5 m) f5) (hf6 : f6 = cf (ml a6 m) (mh a5 m) f5)
    (hr7 : r7 = cr (ml a7 m) (mh a6 m) f6) (hf7 : f7 = cf (ml a7 m) (mh a6 m) f6)
    (hc : c' = (addWithCarry (mh a7 m) 0#64 f7).fst) :
    ((ml a0 m).toNat + c.toNat) % 2 ^ 64 + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat + 2 ^ 256 * r4.toNat + 2 ^ 320 * r5.toNat + 2 ^ 384 * r6.toNat + 2 ^ 448 * r7.toNat + 2 ^ 512 * c'.toNat =
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 + 2 ^ 384 * a6 + 2 ^ 448 * a7) * m.toNat + c.toNat := by
  have e0 : f0.toNat * 2 ^ 64 + ((ml a0 m).toNat + c.toNat) % 2 ^ 64 = (ml a0 m).toNat + c.toNat + false.toNat := by
    have := adc_eq (ml a0 m) c false
    have hf : (addWithCarry (ml a0 m) c false).fst.toNat = ((ml a0 m).toNat + c.toNat) % 2 ^ 64 := by
      simp [addWithCarry, BitVec.toNat_ofNat]
    rw [hf] at this
    rw [hf0]; exact this
  have e1 : f1.toNat * 2 ^ 64 + r1.toNat = (ml a1 m).toNat + (mh a0 m).toNat + f0.toNat := by
    rw [hr1, hf1]; exact adc_eq _ _ _
  have e2 : f2.toNat * 2 ^ 64 + r2.toNat = (ml a2 m).toNat + (mh a1 m).toNat + f1.toNat := by
    rw [hr2, hf2]; exact adc_eq _ _ _
  have e3 : f3.toNat * 2 ^ 64 + r3.toNat = (ml a3 m).toNat + (mh a2 m).toNat + f2.toNat := by
    rw [hr3, hf3]; exact adc_eq _ _ _
  have e4 : f4.toNat * 2 ^ 64 + r4.toNat = (ml a4 m).toNat + (mh a3 m).toNat + f3.toNat := by
    rw [hr4, hf4]; exact adc_eq _ _ _
  have e5 : f5.toNat * 2 ^ 64 + r5.toNat = (ml a5 m).toNat + (mh a4 m).toNat + f4.toNat := by
    rw [hr5, hf5]; exact adc_eq _ _ _
  have e6 : f6.toNat * 2 ^ 64 + r6.toNat = (ml a6 m).toNat + (mh a5 m).toNat + f5.toNat := by
    rw [hr6, hf6]; exact adc_eq _ _ _
  have e7 : f7.toNat * 2 ^ 64 + r7.toNat = (ml a7 m).toNat + (mh a6 m).toNat + f6.toNat := by
    rw [hr7, hf7]; exact adc_eq _ _ _
  have l0 := lohi a0 m ha0
  have l1 := lohi a1 m ha1
  have l2 := lohi a2 m ha2
  have l3 := lohi a3 m ha3
  have l4 := lohi a4 m ha4
  have l5 := lohi a5 m ha5
  have l6 := lohi a6 m ha6
  have l7 := lohi a7 m ha7
  have ec : c'.toNat = (mh a7 m).toNat + f7.toNat := by rw [hc]; exact carry_word _ _ (mh_lt a7 m ha7)
  have fl := fun b : Bool => flag_le b
  simp only [Nat.add_mul, Nat.mul_assoc]
  simp only [Bool.toNat_false] at e0
  omega

theorem lsr3_toNat (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 3 &&& 18446744073709551615#64 &&& 2305843009213693951#64).toNat = n / 8 := by
  have := lsr_ubfm (BitVec.ofNat 64 n) 3 (by decide)
  have e : (2305843009213693951#64) = BitVec.ofNat 64 (2 ^ (64 - 3) - 1) := by decide
  rw [e, this, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  simp [Nat.shiftRight_eq_div_pow]

theorem and7_toNat (n : Nat) : (BitVec.ofNat 64 n &&& 7#64).toNat = n % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  show _ &&& 7 = _
  rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem lsr3_mod (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 3).toNat % 2305843009213693952 = n / 8 := by
  have h := lsr3_toNat n hn
  rw [BitVec.toNat_and, BitVec.toNat_and] at h
  have hr := ((BitVec.ofNat 64 n).rotateRight 3).isLt
  change _ &&& 18446744073709551615 &&& 2305843009213693951 = _ at h
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hr, show (2305843009213693951 : Nat) = 2 ^ 61 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h
  exact h

/-! ### amd64 `MULQ` limb step (Nat form, as the machine-state terms read after `janus64_run`) -/

/-- the value stored by one `mulAddVWW` limb (before the store reduces it mod `2^64`) -/
def nr (a m c : Nat) : Nat := a * m % 18446744073709551616 + c
/-- the new carry word of one `mulAddVWW` limb (`MULQ`, `ADDQ`, `ADCQ $0`) -/
def nc (a m c : Nat) : Nat := a * m / 18446744073709551616 + (decide (18446744073709551616 ≤ a * m % 18446744073709551616 + c)).toNat

theorem q_bound (a m : Nat) (ha : a < 18446744073709551616) (hm : m < 18446744073709551616) :
    a * m / 18446744073709551616 + 1 < 18446744073709551616 := by
  have hp : a * m ≤ 18446744073709551615 * 18446744073709551615 := Nat.mul_le_mul (by omega) (by omega)
  have e : 18446744073709551615 * 18446744073709551615 = 340282366920938463426481119284349108225 := by decide
  have : a * m / 18446744073709551616 < 18446744073709551616 - 1 := Nat.div_lt_of_lt_mul (by omega)
  omega

theorem mul1n (a m c : Nat) (ha : a < 18446744073709551616) (hm : m < 18446744073709551616) (hc : c < 18446744073709551616) :
    nr a m c % 18446744073709551616 + 18446744073709551616 * nc a m c = a * m + c := by
  unfold nr nc
  have h2 := q_bound a m ha hm
  have h1 := Nat.mod_add_div (a * m) (18446744073709551616)
  have h3 : a * m % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  generalize a * m % 18446744073709551616 = r at *
  generalize a * m / 18446744073709551616 = q at *
  by_cases h : 18446744073709551616 ≤ r + c
  · rw [decide_eq_true h, Bool.toNat_true]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

theorem nc_lt (a m c : Nat) (ha : a < 18446744073709551616) (hm : m < 18446744073709551616) :
    nc a m c < 18446744073709551616 := by
  unfold nc
  have h2 := q_bound a m ha hm
  have : (decide (18446744073709551616 ≤ a * m % 18446744073709551616 + c)).toNat ≤ 1 := by
    cases decide (18446744073709551616 ≤ a * m % 18446744073709551616 + c) <;> simp
  generalize a * m / 18446744073709551616 = q at *
  omega

/-- four chained `MULQ` limbs of `mulAddVWW` (amd64 4x block) -/
theorem mulblk4 (a0 a1 a2 a3 m c0 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64)
    (ha3 : a3 < 2 ^ 64) (hm : m < 2 ^ 64) (hc0 : c0 < 2 ^ 64) (c1 c2 c3 : Nat)
    (h1 : c1 = nc a0 m c0) (h2 : c2 = nc a1 m c1) (h3 : c3 = nc a2 m c2) :
    nr a0 m c0 % 2 ^ 64 + 2 ^ 64 * (nr a1 m c1 % 2 ^ 64) + 2 ^ 128 * (nr a2 m c2 % 2 ^ 64) +
      2 ^ 192 * (nr a3 m c3 % 2 ^ 64) + 2 ^ 256 * nc a3 m c3 =
    (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * m + c0 := by
  subst h1 h2 h3
  have l0 := mul1n a0 m c0 ha0 hm hc0
  have l1 := mul1n a1 m (nc a0 m c0) ha1 hm (nc_lt _ _ _ (by assumption) hm)
  have l2 := mul1n a2 m (nc a1 m (nc a0 m c0)) ha2 hm (nc_lt _ _ _ (by assumption) hm)
  have l3 := mul1n a3 m (nc a2 m (nc a1 m (nc a0 m c0))) ha3 hm (nc_lt _ _ _ (by assumption) hm)
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

end FvModexp.Asm
