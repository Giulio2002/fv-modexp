import Janus

/-!
# Multi-limb memory values and carry-step arithmetic for the assembly-kernel summaries

`lv m p n` is the natural number `Σ_{i<n} limb_i · 2^(64 i)` of the `n` little-endian 64-bit limbs at `p`
(`m.readLE p (8 n)`), the model-independent vocabulary of the summaries of `math/big.{addVV, subVV, lshVU, rshVU,
mulAddVWW, addMulVVWW}`.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

/-- the value of the `n` limbs at `p` -/
def lv (m : Memory) (p n : Nat) : Nat := m.readLE p (8 * n)

theorem lv_zero (m : Memory) (p : Nat) : lv m p 0 = 0 := by simp [lv]

theorem pow256_eq (n : Nat) : 256 ^ (8 * n) = 2 ^ (64 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega

theorem lv_lt (m : Memory) (p n : Nat) : lv m p n < 2 ^ (64 * n) := by
  unfold lv; have := Memory.readLE_lt m p (8 * n); rwa [pow256_eq] at this

theorem lv_succ (m : Memory) (p n : Nat) :
    lv m p (n + 1) = lv m p n + 2 ^ (64 * n) * m.readLE (p + 8 * n) 8 := by
  unfold lv
  rw [show 8 * (n + 1) = 8 * n + 8 by omega, Memory.readLE_add, pow256_eq]

theorem limb_lt (m : Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 := by
  have := Memory.readLE_lt m a 8; simpa using this

/-- writing limb `n` after the `n` limbs below it -/
theorem lv_write_succ (m : Memory) (p n v : Nat) :
    lv (m.writeLE (p + 8 * n) 8 v) p (n + 1) = lv m p n + 2 ^ (64 * n) * (v % 2 ^ 64) := by
  rw [lv_succ, Memory.readLE_writeLE_self]
  unfold lv
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

/-- a store just above the frame range extends it -/
theorem frame_ext {m m' : Memory} {z i : Nat} (h : MemFrame m m' [(z, z + 8 * i)]) (v : Nat) :
    MemFrame m (m'.writeLE (z + 8 * i) 8 v) [(z, z + 8 * (i + 1))] :=
  ⟨fun a n ha => by
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at ha
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h.readLE a n (by simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega),
   fun a n w => by rw [Memory.accessible_writeLE]; exact h.accessible a n w⟩

theorem frame_zero (m : Memory) (z : Nat) : MemFrame m m [(z, z + 8 * 0)] := MemFrame.refl _ _

/-- widening a range list never hurts, as a store-result relation -/
theorem frame_mono {m m' : Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (hs : ∀ a n, Janus.Outside a n rs' → Janus.Outside a n rs) : MemFrame m m' rs' :=
  ⟨fun a n ha => h.readLE a n (hs a n ha), h.accessible⟩

/-- the carry step of one limb: `Z + P·C = A + B`, `a + b + C = r + 2^64·C'` gives
`Z + P·r + (P·2^64)·C' = (A + P·a) + (B + P·b)` -/
theorem add_step (P W Z C A B a b r C' : Nat) (hs : Z + P * C = A + B)
    (ht : r + W * C' = a + b + C) :
    Z + P * r + (P * W) * C' = (A + P * a) + (B + P * b) := by
  have h1 : P * (r + W * C') = P * (a + b + C) := by rw [ht]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc] at h1
  omega


theorem pow_succ64 (i : Nat) : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem lv_add4 (m : Memory) (p i : Nat) :
    lv m p (i + 4) = lv m p i + 2 ^ (64 * i) * (m.readLE (p + 8 * i) 8 + 2 ^ 64 * m.readLE (p + 8 * i + 8) 8 +
      2 ^ 128 * m.readLE (p + 8 * i + 16) 8 + 2 ^ 192 * m.readLE (p + 8 * i + 24) 8) := by
  have e1 := lv_succ m p i
  have e2 := lv_succ m p (i + 1)
  have e3 := lv_succ m p (i + 2)
  have e4 := lv_succ m p (i + 3)
  rw [show i + 1 + 1 = i + 2 from rfl] at e2
  rw [show i + 2 + 1 = i + 3 from rfl] at e3
  rw [show i + 3 + 1 = i + 4 from rfl] at e4
  rw [pow_succ64] at e2
  rw [show 64 * (i + 2) = 64 * (i + 1) + 64 by omega, Nat.pow_add, pow_succ64] at e3
  rw [show 64 * (i + 3) = 64 * (i + 1) + 64 + 64 by omega, Nat.pow_add, Nat.pow_add, pow_succ64] at e4
  rw [show p + 8 * (i + 1) = p + 8 * i + 8 by omega] at e2
  rw [show p + 8 * (i + 2) = p + 8 * i + 16 by omega] at e3
  rw [show p + 8 * (i + 3) = p + 8 * i + 24 by omega] at e4
  rw [e4, e3, e2, e1]
  have : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  have h3 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add, ← Nat.pow_add]
  rw [this, h3]
  simp only [Nat.mul_add, Nat.mul_assoc]
  omega

theorem lv_write4 (m : Memory) (p i v0 v1 v2 v3 : Nat) :
    lv ((((m.writeLE (p + 8 * i) 8 v0).writeLE (p + 8 * i + 8) 8 v1).writeLE (p + 8 * i + 16) 8 v2).writeLE
        (p + 8 * i + 24) 8 v3) p (i + 4) =
      lv m p i + 2 ^ (64 * i) * (v0 % 2 ^ 64 + 2 ^ 64 * (v1 % 2 ^ 64) + 2 ^ 128 * (v2 % 2 ^ 64) +
        2 ^ 192 * (v3 % 2 ^ 64)) := by
  have e1 := lv_write_succ m p i v0
  have e2 := lv_write_succ (m.writeLE (p + 8 * i) 8 v0) p (i + 1) v1
  have e3 := lv_write_succ ((m.writeLE (p + 8 * i) 8 v0).writeLE (p + 8 * i + 8) 8 v1) p (i + 2) v2
  have e4 := lv_write_succ (((m.writeLE (p + 8 * i) 8 v0).writeLE (p + 8 * i + 8) 8 v1).writeLE
    (p + 8 * i + 16) 8 v2) p (i + 3) v3
  rw [show p + 8 * (i + 1) = p + 8 * i + 8 by omega] at e2
  rw [show p + 8 * (i + 2) = p + 8 * i + 16 by omega] at e3
  rw [show p + 8 * (i + 3) = p + 8 * i + 24 by omega] at e4
  rw [show i + 1 + 1 = i + 2 from rfl] at e2
  rw [show i + 2 + 1 = i + 3 from rfl] at e3
  rw [show i + 3 + 1 = i + 4 from rfl] at e4
  rw [e4, e3, e2, e1]
  rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
  rw [show 64 * (i + 2) = 64 * i + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  rw [show 64 * (i + 3) = 64 * i + 64 + 64 + 64 by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  have h2 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  have h3 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add, ← Nat.pow_add]
  rw [h2, h3]
  simp only [Nat.mul_add, Nat.mul_assoc]
  omega

theorem frame_ext4 {m m' : Memory} {z i : Nat} (h : MemFrame m m' [(z, z + 8 * i)]) (v0 v1 v2 v3 : Nat) :
    MemFrame m ((((m'.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2).writeLE
      (z + 8 * i + 24) 8 v3) [(z, z + 8 * (i + 4))] := by
  have := frame_ext (frame_ext (frame_ext (frame_ext h v0) v1) v2) v3
  rw [show z + 8 * (i + 1) = z + 8 * i + 8 by omega, show z + 8 * (i + 1 + 1) = z + 8 * i + 16 by omega,
    show z + 8 * (i + 1 + 1 + 1) = z + 8 * i + 24 by omega] at this
  exact this


theorem pow_i4 (i : Nat) : 2 ^ (64 * (i + 4)) = 2 ^ (64 * i) * 2 ^ 256 := by
  rw [Nat.mul_add, Nat.pow_add]

theorem toNat_mod64 (v : BitVec 64) : v.toNat % 2 ^ 64 = v.toNat := Nat.mod_eq_of_lt v.isLt


/-- `UBFM`/`LSR #k` as the compiler emits it (adapted from fv-uint256 `Fv256.Arm64.Div64.lsr_ubfm`) -/
theorem lsr_ubfm (u : BitVec 64) (k : Nat) (hk : k < 64) :
    (u.rotateRight k &&& 18446744073709551615#64 &&& BitVec.ofNat 64 (2 ^ (64 - k) - 1)) = u >>> k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (BitVec.ofNat 64 (2 ^ (64 - k) - 1)).getLsbD i = decide (i < 64 - k) := by
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight, this,
    show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes, hi]
  by_cases h : i < 64 - k
  · simp [h, Nat.mod_eq_of_lt hk]
  · simp [h]; apply BitVec.getLsbD_of_ge; omega

theorem lsr2_toNat (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64).toNat = n / 4 := by
  have := lsr_ubfm (BitVec.ofNat 64 n) 2 (by decide)
  have e : (4611686018427387903#64) = BitVec.ofNat 64 (2 ^ (64 - 2) - 1) := by decide
  rw [e, this, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  simp [Nat.shiftRight_eq_div_pow]

theorem and3_toNat (n : Nat) : (BitVec.ofNat 64 n &&& 3#64).toNat = n % 4 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  show _ &&& 3 = _
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega


theorem lsr2_mod (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 2).toNat % 4611686018427387904 = n / 4 := by
  have h := lsr2_toNat n hn
  rw [BitVec.toNat_and, BitVec.toNat_and] at h
  have hr := ((BitVec.ofNat 64 n).rotateRight 2).isLt
  change _ &&& 18446744073709551615 &&& 4611686018427387903 = _ at h
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hr, show (4611686018427387903 : Nat) = 2 ^ 62 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h
  exact h

end FvModexp.Asm
