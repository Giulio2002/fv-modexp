import FvModexp.Proofs.Common.Conv

/-!
# The arithmetic of `nat.setBytes` (`nat.go:1665`, both copies), ISA independent

```go
func (z nat) setBytes(buf []byte) nat {
	z = z.make((len(buf) + _S - 1) / _S)
	i := len(buf)
	for k := 0; i >= _S; k++ { z[k] = bigEndianWord(buf[i-_S : i]); i -= _S }     // word loop
	if i > 0 {
		var d Word
		for s := uint(0); i > 0; s += 8 { d |= Word(buf[i-1]) << s; i-- }        // byte loop
		z[len(z)-1] = d
	}
	return z.norm()                                                                  // norm loop
}
```

Word loop: after `k` iterations the first `k` limbs hold the last `8k` bytes (`natVal = beVal (bp + bl - 8k) (8k)`).
Byte loop: after `t` iterations `d` holds the `t` bytes before `bp + i0` (`d = beVal (bp + i0 - t) t`, shift `8t`).
-/

namespace FvModexp

open Janus Janus.Arm64

/-- One more word: the 8 bytes before a big-endian block are its high limb. -/
theorem beVal_word_step (m : Memory) (a k : Nat) :
    beVal m a (8 * (k + 1)) = beVal m (a + 8) (8 * k) + 2 ^ (64 * k) * beVal m a 8 := by
  rw [show 8 * (k + 1) = 8 + 8 * k by omega, beVal_add,
    show (256 : Nat) ^ (8 * k) = 2 ^ (64 * k) by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega]
  rw [Nat.mul_comm (8 : Nat) k, Nat.mul_comm (beVal m a 8), Nat.add_comm]

/-- One more byte below a big-endian block of `t` bytes. -/
theorem beVal_byte_step (m : Memory) (a t : Nat) :
    beVal m a (t + 1) = beVal m (a + 1) t + (m.bytes a).toNat * 2 ^ (8 * t) := by
  rw [show t + 1 = 1 + t by omega, beVal_add,
    show (256 : Nat) ^ t = 2 ^ (8 * t) by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]]
  simp only [beVal_succ, beVal_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  rw [Nat.add_comm]

/-- `d ||| (b << 8t)` with `d < 2^(8t)` is the sum. -/
theorem or_shift_eq_add (d b t : Nat) (hd : d < 2 ^ (8 * t)) :
    d ||| b * 2 ^ (8 * t) = d + b * 2 ^ (8 * t) := by
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hd, Nat.add_comm]

/-- The last limb on top of the full words: the whole buffer. -/
theorem beVal_top (m : Memory) (bp q r : Nat) :
    beVal m bp (r + 8 * q) = beVal m (bp + r) (8 * q) + 2 ^ (64 * q) * beVal m bp r := by
  rw [beVal_add, show (256 : Nat) ^ (8 * q) = 2 ^ (64 * q) by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega]
  rw [Nat.mul_comm (8 : Nat) q, Nat.mul_comm (beVal m bp r), Nat.add_comm]

/-- Limbs below a store keep their value. -/
theorem natVal_writeLE_above (m : Memory) (p k a v : Nat) (h : p + 8 * k ≤ a) :
    natVal (m.writeLE a 8 v) p k = natVal m p k :=
  Memory.readLE_writeLE_of_disjoint _ _ (Or.inl h)

/-- Storing limb `k`. -/
theorem natVal_store_top (m : Memory) (p k v : Nat) (hv : v < 2 ^ 64) :
    natVal (m.writeLE (p + 8 * k) 8 v) p (k + 1) = natVal m p k + 2 ^ (64 * k) * v := by
  rw [natVal_succ, natVal_writeLE_above _ _ _ _ _ (Nat.le_refl _), Memory.readLE_writeLE_self,
    Nat.mod_eq_of_lt (by simpa using hv)]

/-- A zero top limb does not count. -/
theorem natVal_zero_top (m : Memory) (p k : Nat) (h : m.readLE (p + 8 * k) 8 = 0) :
    natVal m p (k + 1) = natVal m p k := by
  rw [natVal_succ, h, Nat.mul_zero, Nat.add_zero]

end FvModexp

namespace FvModexp

open Janus Janus.Arm64

/-- One iteration of the byte loop as the arm64 executor leaves it (`LSL` by `SH`, `CSEL` on `SH < 64`, `ORR`). -/
theorem byte_or_step (m : Memory) (a t : Nat) (ht : t < 8) (D SH : BitVec 64) (hSH : SH.toNat = 8 * t)
    (hD : D.toNat = beVal m (a + 1) t) :
    (D ||| (if SH.toNat < 64 then BitVec.ofNat 64 (m.readLE a 1 * 2 ^ (SH.toNat % 64)) else 0#64)).toNat =
      beVal m a (t + 1) := by
  have hlt : SH.toNat < 64 := by omega
  rw [ite_eq_left hlt, BitVec.toNat_or, BitVec.toNat_ofNat, hSH, Nat.mod_eq_of_lt (show 8 * t < 64 by omega)]
  have hb := (m.bytes a).isLt
  have hpow : 2 ^ (8 * t) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hprod : (m.bytes a).toNat * 2 ^ (8 * t) < 2 ^ 64 := by
    calc (m.bytes a).toNat * 2 ^ (8 * t) < 256 * 2 ^ 56 :=
          Nat.mul_lt_mul_of_lt_of_le hb hpow (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by decide
  simp only [Memory.readLE_one]
  rw [Nat.mod_eq_of_lt hprod, hD, or_shift_eq_add _ _ _ (by
    have := beVal_lt m (a + 1) t
    rwa [show (256 : Nat) ^ t = 2 ^ (8 * t) by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]] at this),
    beVal_byte_step]

end FvModexp

namespace FvModexp

open Janus Janus.Arm64

theorem byte64_toNat (m : Memory) (a : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE a 1)))).toNat = (m.bytes a).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Memory.readLE_one]
  have := (m.bytes a).isLt
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- One iteration of the byte loop as the amd64 executor leaves it (`SHLQ CL`, the `SBBQ` mask, `ORQ`). -/
theorem byte_or_step64 (m : Memory) (a t : Nat) (ht : t < 8) (D SH : BitVec 64) (hSH : SH.toNat = 8 * t)
    (hD : D.toNat = beVal m (a + 1) t) :
    (D ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE a 1))) <<< (SH.toNat % 64) &&&
      if SH.toNat < 64 then 18446744073709551615#64 else 0#64)).toNat = beVal m a (t + 1) := by
  have hlt : SH.toNat < 64 := by omega
  rw [if_pos hlt]
  have hb := (m.bytes a).isLt
  have hpow : 2 ^ (8 * t) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hprod : (m.bytes a).toNat * 2 ^ (8 * t) < 2 ^ 64 := by
    calc (m.bytes a).toNat * 2 ^ (8 * t) < 256 * 2 ^ 56 :=
          Nat.mul_lt_mul_of_lt_of_le hb hpow (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by decide
  have h1 : (18446744073709551615#64).toNat = 2 ^ 64 - 1 := rfl
  rw [BitVec.toNat_or, BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_shiftLeft, byte64_toNat,
    hSH, Nat.mod_eq_of_lt (show 8 * t < 64 by omega), Nat.shiftLeft_eq, Nat.mod_mod, Nat.mod_eq_of_lt hprod, hD,
    or_shift_eq_add _ _ _ (by
      have := beVal_lt m (a + 1) t
      rwa [show (256 : Nat) ^ t = 2 ^ (8 * t) by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]] at this),
    beVal_byte_step]

end FvModexp

namespace FvModexp

open Janus Janus.Arm64

/-- The same when the executor took `SHLQ CL` with `CL = 0` (no shift: the first byte, `t = 0`). -/
theorem byte_or_step64_zero (m : Memory) (a t : Nat) (D SH : BitVec 64) (hSH : SH.toNat = 8 * t) (h0 : SH.toNat % 64 = 0)
    (ht : t < 8) (hD : D.toNat = beVal m (a + 1) t) :
    (D ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE a 1))) &&&
      if SH.toNat < 64 then 18446744073709551615#64 else 0#64)).toNat = beVal m a (t + 1) := by
  have ht0 : t = 0 := by omega
  subst ht0
  have := byte_or_step64 m a 0 (by omega) D SH hSH hD
  rwa [h0, BitVec.shiftLeft_zero] at this

end FvModexp
