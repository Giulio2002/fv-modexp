import FvModexp.Proofs.Common.AsmMul

/-!
# arm64 `addMulVVWW` limb arithmetic (`UMULH`/`MUL`, `ADDS`/`ADCS` chains, `ADC ZR`)

`addmul1`: the one-limb step (arith_arm64.s loop1 of `addMulVVWW`); `addmulblk8`: the eight-limb block (loop8): the
products `y_j·m` with the incoming carry word, then the `x_j` added by a second carry chain, the final carry word `C`.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

theorem adc0 (h : BitVec 64) (f : Bool) : (addWithCarry h 0#64 f).fst.toNat = (h.toNat + f.toNat) % 2 ^ 64 := by
  simp [addWithCarry, BitVec.toNat_ofNat]

/-- `y·m + c` (low word `cr (ml b m) c false`, high word `mh b m + flag`), then `+ x` with the carry into the high word -/
theorem addmul1 (xa b : Nat) (m c : BitVec 64) (hxa : xa < 2 ^ 64) (hb : b < 2 ^ 64) :
    (cr (cr (ml b m) c false) (BitVec.ofNat 64 xa) false).toNat +
      2 ^ 64 * (addWithCarry (addWithCarry (mh b m) 0#64 (cf (ml b m) c false)).fst 0#64
        (cf (cr (ml b m) c false) (BitVec.ofNat 64 xa) false)).fst.toNat =
    xa + b * m.toNat + c.toNat := by
  have e1 := adc_eq (ml b m) c false
  have e2 := adc_eq (cr (ml b m) c false) (BitVec.ofNat 64 xa) false
  have h1 := carry_word (mh b m) (cf (ml b m) c false) (mh_lt b m hb)
  have h2 := adc0 (addWithCarry (mh b m) 0#64 (cf (ml b m) c false)).fst (cf (cr (ml b m) c false) (BitVec.ofNat 64 xa) false)
  have l := lohi b m hb
  have hm := m.isLt
  have hc := c.isLt
  have hp : b * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by decide
  have f1 := flag_le (cf (ml b m) c false)
  have f2 := flag_le (cf (cr (ml b m) c false) (BitVec.ofNat 64 xa) false)
  simp only [cr, cf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxa, Bool.toNat_false] at e1 e2 h1 h2 ⊢
  rw [h1] at h2
  rw [h2]
  have : (mh b m).toNat + (addWithCarry (ml b m) c false).snd.c.toNat +
      (addWithCarry (addWithCarry (ml b m) c false).fst (BitVec.ofNat 64 xa) false).snd.c.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

set_option exponentiation.threshold 1024 in
/-- the eight-limb block: `Σ s_j 2^(64 j) + 2^512·C = X8 + Y8·m + c` -/
theorem addmulblk8 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (ha4 : a4 < 2 ^ 64)
    (ha5 : a5 < 2 ^ 64) (ha6 : a6 < 2 ^ 64) (ha7 : a7 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64) (hb4 : b4 < 2 ^ 64)
    (hb5 : b5 < 2 ^ 64) (hb6 : b6 < 2 ^ 64) (hb7 : b7 < 2 ^ 64) (m c : BitVec 64)
    (r1 r2 r3 r4 r5 r6 r7 c' : BitVec 64) (f0 f1 f2 f3 f4 f5 f6 f7 : Bool)
    (hf0 : f0 = cf (ml a0 m) c false)
    (hr1 : r1 = cr (ml a1 m) (mh a0 m) f0) (hf1 : f1 = cf (ml a1 m) (mh a0 m) f0)
    (hr2 : r2 = cr (ml a2 m) (mh a1 m) f1) (hf2 : f2 = cf (ml a2 m) (mh a1 m) f1)
    (hr3 : r3 = cr (ml a3 m) (mh a2 m) f2) (hf3 : f3 = cf (ml a3 m) (mh a2 m) f2)
    (hr4 : r4 = cr (ml a4 m) (mh a3 m) f3) (hf4 : f4 = cf (ml a4 m) (mh a3 m) f3)
    (hr5 : r5 = cr (ml a5 m) (mh a4 m) f4) (hf5 : f5 = cf (ml a5 m) (mh a4 m) f4)
    (hr6 : r6 = cr (ml a6 m) (mh a5 m) f5) (hf6 : f6 = cf (ml a6 m) (mh a5 m) f5)
    (hr7 : r7 = cr (ml a7 m) (mh a6 m) f6) (hf7 : f7 = cf (ml a7 m) (mh a6 m) f6)
    (hc : c' = (addWithCarry (mh a7 m) 0#64 f7).fst)
    (s1 s2 s3 s4 s5 s6 s7 : BitVec 64) (g0 g1 g2 g3 g4 g5 g6 g7 : Bool)
    (hg0 : g0 = cf (ml a0 m + c) (BitVec.ofNat 64 b0) false)
    (hs1 : s1 = cr r1 (BitVec.ofNat 64 b1) g0) (hg1 : g1 = cf r1 (BitVec.ofNat 64 b1) g0)
    (hs2 : s2 = cr r2 (BitVec.ofNat 64 b2) g1) (hg2 : g2 = cf r2 (BitVec.ofNat 64 b2) g1)
    (hs3 : s3 = cr r3 (BitVec.ofNat 64 b3) g2) (hg3 : g3 = cf r3 (BitVec.ofNat 64 b3) g2)
    (hs4 : s4 = cr r4 (BitVec.ofNat 64 b4) g3) (hg4 : g4 = cf r4 (BitVec.ofNat 64 b4) g3)
    (hs5 : s5 = cr r5 (BitVec.ofNat 64 b5) g4) (hg5 : g5 = cf r5 (BitVec.ofNat 64 b5) g4)
    (hs6 : s6 = cr r6 (BitVec.ofNat 64 b6) g5) (hg6 : g6 = cf r6 (BitVec.ofNat 64 b6) g5)
    (hs7 : s7 = cr r7 (BitVec.ofNat 64 b7) g6) (hg7 : g7 = cf r7 (BitVec.ofNat 64 b7) g6) :
    ((ml a0 m).toNat + c.toNat + b0) % 2 ^ 64 + 2 ^ 64 * s1.toNat + 2 ^ 128 * s2.toNat + 2 ^ 192 * s3.toNat + 2 ^ 256 * s4.toNat +
      2 ^ 320 * s5.toNat + 2 ^ 384 * s6.toNat + 2 ^ 448 * s7.toNat +
      2 ^ 512 * (addWithCarry c' 0#64 g7).fst.toNat =
    (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3 + 2 ^ 256 * b4 + 2 ^ 320 * b5 + 2 ^ 384 * b6 + 2 ^ 448 * b7) +
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 + 2 ^ 384 * a6 + 2 ^ 448 * a7) *
        m.toNat + c.toNat := by
  have hmul := mulblk8 a0 a1 a2 a3 a4 a5 a6 a7 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 m c r1 r2 r3 r4 r5 r6 r7 c'
    f0 f1 f2 f3 f4 f5 f6 f7 hf0 hr1 hf1 hr2 hf2 hr3 hf3 hr4 hf4 hr5 hf5 hr6 hf6 hr7 hf7 hc
  have t0 : (cr (ml a0 m) c false).toNat = ((ml a0 m).toNat + c.toNat) % 2 ^ 64 := by
    simp [cr, addWithCarry, BitVec.toNat_ofNat]
  have hbn : ∀ b, b < 2 ^ 64 → (BitVec.ofNat 64 b).toNat = b := fun b hb => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  have e0 : g0.toNat * 2 ^ 64 + ((ml a0 m).toNat + c.toNat + b0) % 2 ^ 64 = ((ml a0 m).toNat + c.toNat) % 2 ^ 64 + b0 := by
    have := adc_eq (ml a0 m + c) (BitVec.ofNat 64 b0) false
    have hf : (addWithCarry (ml a0 m + c) (BitVec.ofNat 64 b0) false).fst.toNat =
        ((ml a0 m).toNat + c.toNat + b0) % 2 ^ 64 := by
      simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_add, Bool.toNat_false, Nat.add_zero,
        Nat.mod_eq_of_lt hb0]
      rw [Nat.mod_add_mod]
    rw [hf, hbn b0 hb0, BitVec.toNat_add] at this
    rw [hg0]; simp only [Bool.toNat_false, Nat.add_zero] at this; exact this
  have e1 : g1.toNat * 2 ^ 64 + s1.toNat = r1.toNat + b1 + g0.toNat := by
    rw [hs1, hg1]; have := adc_eq r1 (BitVec.ofNat 64 b1) g0; rw [hbn b1 hb1] at this; exact this
  have e2 : g2.toNat * 2 ^ 64 + s2.toNat = r2.toNat + b2 + g1.toNat := by
    rw [hs2, hg2]; have := adc_eq r2 (BitVec.ofNat 64 b2) g1; rw [hbn b2 hb2] at this; exact this
  have e3 : g3.toNat * 2 ^ 64 + s3.toNat = r3.toNat + b3 + g2.toNat := by
    rw [hs3, hg3]; have := adc_eq r3 (BitVec.ofNat 64 b3) g2; rw [hbn b3 hb3] at this; exact this
  have e4 : g4.toNat * 2 ^ 64 + s4.toNat = r4.toNat + b4 + g3.toNat := by
    rw [hs4, hg4]; have := adc_eq r4 (BitVec.ofNat 64 b4) g3; rw [hbn b4 hb4] at this; exact this
  have e5 : g5.toNat * 2 ^ 64 + s5.toNat = r5.toNat + b5 + g4.toNat := by
    rw [hs5, hg5]; have := adc_eq r5 (BitVec.ofNat 64 b5) g4; rw [hbn b5 hb5] at this; exact this
  have e6 : g6.toNat * 2 ^ 64 + s6.toNat = r6.toNat + b6 + g5.toNat := by
    rw [hs6, hg6]; have := adc_eq r6 (BitVec.ofNat 64 b6) g5; rw [hbn b6 hb6] at this; exact this
  have e7 : g7.toNat * 2 ^ 64 + s7.toNat = r7.toNat + b7 + g6.toNat := by
    rw [hs7, hg7]; have := adc_eq r7 (BitVec.ofNat 64 b7) g6; rw [hbn b7 hb7] at this; exact this
  rw [adc0]
  -- value of the products block and the bound that keeps the final carry word from wrapping
  have hY : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 + 2 ^ 384 * a6 +
      2 ^ 448 * a7) < 2 ^ 512 := by omega
  have hm := m.isLt
  have hYm : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 + 2 ^ 384 * a6 +
      2 ^ 448 * a7) * m.toNat ≤ (2 ^ 512 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 + 2 ^ 384 * a6 +
      2 ^ 448 * a7) * m.toNat = YM at hmul hYm ⊢
  have fl := fun b : Bool => flag_le b
  have hc' := c.isLt
  have hcw : c'.toNat + g7.toNat < 2 ^ 64 := by
    have := fl g0; have := fl g1; have := fl g2; have := fl g3; have := fl g4; have := fl g5; have := fl g6
    have := fl g7
    have := s1.isLt; have := s2.isLt; have := s3.isLt; have := s4.isLt; have := s5.isLt
    have := s6.isLt; have := s7.isLt
    have := r1.isLt; have := r2.isLt; have := r3.isLt; have := r4.isLt; have := r5.isLt; have := r6.isLt
    have := r7.isLt
    omega
  rw [Nat.mod_eq_of_lt hcw]
  have := fl g0; have := fl g1; have := fl g2; have := fl g3; have := fl g4; have := fl g5; have := fl g6
  have := fl g7
  omega

end FvModexp.Asm
