import FvModexp.Proofs.Common.AsmLimbs

/-!
# Shared lemmas for the `math/big.{lshVU, rshVU}` summaries (arm64 and amd64)

Nat-level facts about the word shifts (`1 <= s <= 63`): the split `v * 2^s = hi * 2^64 + lo`, the `OR` of the two
partial words as a sum, and the one-limb step of the shift invariants (`lsh_step`, `rsh_step`).
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

theorem lv_split (m : Memory) (p a b : Nat) :
    lv m p (a + b) = lv m p a + 2 ^ (64 * a) * lv m (p + 8 * a) b := by
  unfold lv
  rw [show 8 * (a + b) = 8 * a + 8 * b by omega, Memory.readLE_add, pow256_eq]

theorem lv_cons (m : Memory) (p t : Nat) :
    lv m p (t + 1) = m.readLE p 8 + 2 ^ 64 * lv m (p + 8) t := by
  have := lv_split m p 1 t
  rw [show 1 + t = t + 1 by omega] at this
  rw [this]; simp [lv, Nat.mul_one]

/-- the high part of the shifted word -/
theorem shl_split (v s : Nat) (hv : v < 2 ^ 64) (h1 : 1 ≤ s) (h2 : s ≤ 63) :
    v * 2 ^ s = (v / 2 ^ (64 - s)) * 2 ^ 64 + (v * 2 ^ s) % 2 ^ 64 := by
  have e : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have h : v * 2 ^ s % 2 ^ 64 = 2 ^ s * (v % 2 ^ (64 - s)) := by
    rw [Nat.mul_comm v, e, Nat.mul_mod_mul_left]
  rw [h, e]
  have := Nat.div_add_mod v (2 ^ (64 - s))
  calc v * 2 ^ s = (2 ^ (64 - s) * (v / 2 ^ (64 - s)) + v % 2 ^ (64 - s)) * 2 ^ s := by rw [this]
    _ = _ := by
      simp only [Nat.add_mul, Nat.mul_add]
      rw [show 2 ^ (64 - s) * (v / 2 ^ (64 - s)) * 2 ^ s = v / 2 ^ (64 - s) * (2 ^ s * 2 ^ (64 - s)) by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      rw [Nat.mul_comm (v % 2 ^ (64 - s))]

theorem hi_lt (v s : Nat) (hv : v < 2 ^ 64) (h1 : 1 ≤ s) (h2 : s ≤ 63) : v / 2 ^ (64 - s) < 2 ^ s := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  have : s + (64 - s) = 64 := by omega
  rw [this]; exact hv

theorem shl_lo_eq (v s : Nat) (h1 : 1 ≤ s) (h2 : s ≤ 63) :
    v * 2 ^ s % 2 ^ 64 = 2 ^ s * (v % 2 ^ (64 - s)) := by
  have e : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.mul_comm v, e, Nat.mul_mod_mul_left]

/-- `(a >>> (64-s)) ||| (b << s)` as a sum, for `a, b < 2^64` -/
theorem or_shift (a b s : Nat) (ha : a < 2 ^ 64) (h1 : 1 ≤ s) (h2 : s ≤ 63) :
    (a / 2 ^ (64 - s)) ||| (b * 2 ^ s % 2 ^ 64) = a / 2 ^ (64 - s) + b * 2 ^ s % 2 ^ 64 := by
  rw [shl_lo_eq b s h1 h2, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (hi_lt a s ha h1 h2)]
  omega

/-- one limb of `lshVU` (processing `x[j]` above the already consumed limbs; `R` is the pending partial word of `z[j+1]`) -/
theorem lsh_step (X C Zup R Xl v j n s : Nat) (hv : v < 2 ^ 64) (h1 : 1 ≤ s) (h2 : s ≤ 63)
    (hI : X * 2 ^ s = C * 2 ^ (64 * n) + 2 ^ (64 * (j + 2)) * Zup + 2 ^ (64 * (j + 1)) * R +
      (Xl + 2 ^ (64 * j) * v) * 2 ^ s) :
    X * 2 ^ s = C * 2 ^ (64 * n) + 2 ^ (64 * (j + 1)) * ((v / 2 ^ (64 - s) + R) + 2 ^ 64 * Zup) +
      2 ^ (64 * j) * (v * 2 ^ s % 2 ^ 64) + Xl * 2 ^ s := by
  have e := shl_split v s hv h1 h2
  have p1 : 2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  have p2 : 2 ^ (64 * (j + 2)) = 2 ^ (64 * j) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (j + 2) = 64 * j + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  rw [p1, p2] at hI
  rw [p1]
  have h3 : (Xl + 2 ^ (64 * j) * v) * 2 ^ s = Xl * 2 ^ s + 2 ^ (64 * j) * ((v / 2 ^ (64 - s)) * 2 ^ 64 +
      (v * 2 ^ s) % 2 ^ 64) := by rw [Nat.add_mul, Nat.mul_assoc, ← e]
  rw [h3] at hI
  generalize 2 ^ (64 * j) = P at *
  generalize 2 ^ 64 = W at *
  generalize v / 2 ^ (64 - s) = hi at *
  generalize v * 2 ^ s % 2 ^ 64 = lo at *
  generalize C * 2 ^ (64 * n) = CN at *
  grind

theorem shift_sum_lt (a b sh : Nat) (ha : a < 2 ^ 64) (h1 : 1 ≤ sh) (h2 : sh ≤ 63) :
    a / 2 ^ (64 - sh) + b * 2 ^ sh % 2 ^ 64 < 2 ^ 64 := by
  have e : (2 : Nat) ^ 64 = 2 ^ sh * 2 ^ (64 - sh) := by rw [← Nat.pow_add]; congr 1; omega
  have hh := hi_lt a sh ha h1 h2
  have hm := Nat.mod_lt b (Nat.two_pow_pos (64 - sh))
  have hl : 2 ^ sh * (b % 2 ^ (64 - sh) + 1) ≤ 2 ^ sh * 2 ^ (64 - sh) := Nat.mul_le_mul_left _ hm
  rw [Nat.mul_add, Nat.mul_one] at hl
  rw [shl_lo_eq b sh h1 h2]
  omega

/-- the written word of one step: `(a >>> (64-s)) ||| (b << s)` (as the machine computes it), reduced mod `2^64` -/
theorem or_wr (a b sh k : Nat) (ha : a < 2 ^ 64) (h1 : 1 ≤ sh) (h2 : sh ≤ 63) (hk : k = 64 - sh) :
    ((BitVec.ofNat 64 a >>> k).toNat ||| b * 2 ^ sh % 18446744073709551616) % 2 ^ 64 =
      a / 2 ^ (64 - sh) + b * 2 ^ sh % 2 ^ 64 := by
  subst hk
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow,
    show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, or_shift a b sh ha h1 h2]
  exact Nat.mod_eq_of_lt (shift_sum_lt a b sh ha h1 h2)

/-- the invariant of the backward shift loops: with `m0` the memory at the entry, `x[0..j-1]` unread, `x[j]` consumed,
`z[j+1..n-1]` written in `M` and `c` (the carry-out word) is `C` -/
def LInv (m0 M : Memory) (x z n sh j t C : Nat) : Prop :=
  lv m0 x n * 2 ^ sh = C * 2 ^ (64 * n) + 2 ^ (64 * (j + 1)) * lv M (z + 8 * (j + 1)) t +
    2 ^ (64 * j) * (m0.readLE (x + 8 * j) 8 * 2 ^ sh % 2 ^ 64) + lv m0 x j * 2 ^ sh

theorem lv_wr {m : Memory} {p q t v : Nat} (h : q + 8 ≤ p) :
    lv (m.writeLE q 8 v) p t = lv m p t := by
  unfold lv; exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)

theorem linv_step1 (m0 M : Memory) (x z n sh j t C w : Nat) (h1 : 1 ≤ sh) (h2 : sh ≤ 63)
    (hI : LInv m0 M x z n sh (j + 1) t C)
    (hw : w % 2 ^ 64 = m0.readLE (x + 8 * j) 8 / 2 ^ (64 - sh) + m0.readLE (x + 8 * (j + 1)) 8 * 2 ^ sh % 2 ^ 64) :
    LInv m0 (M.writeLE (z + 8 * (j + 1)) 8 w) x z n sh j (t + 1) C := by
  unfold LInv at hI ⊢
  rw [lv_succ m0 x j] at hI
  have key := lsh_step (lv m0 x n) C (lv M (z + 8 * (j + 1 + 1)) t) (m0.readLE (x + 8 * (j + 1)) 8 * 2 ^ sh % 2 ^ 64)
    (lv m0 x j) (m0.readLE (x + 8 * j) 8) j n sh (limb_lt _ _) h1 h2 hI
  rw [lv_cons, Memory.readLE_writeLE_self, hw,
    show z + 8 * (j + 1) + 8 = z + 8 * (j + 1 + 1) by omega, lv_wr (by omega)]
  exact key

theorem lv_w4 (m : Memory) (p t a b c d : Nat) :
    lv (((m.writeLE p 8 a).writeLE (p + 8) 8 b).writeLE (p + 16) 8 c |>.writeLE (p + 24) 8 d) p (4 + t) =
      a % 2 ^ 64 + 2 ^ 64 * (b % 2 ^ 64) + 2 ^ 128 * (c % 2 ^ 64) + 2 ^ 192 * (d % 2 ^ 64) +
        2 ^ 256 * lv m (p + 32) t := by
  have h := lv_write4 m p 0 a b c d
  simp only [Nat.mul_zero, Nat.add_zero, lv_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at h
  rw [lv_split, h, show 64 * 4 = 256 by rfl]
  have : lv ((((m.writeLE p 8 a).writeLE (p + 8) 8 b).writeLE (p + 16) 8 c).writeLE (p + 24) 8 d) (p + 8 * 4) t =
      lv m (p + 32) t := by
    rw [lv_wr (by omega), lv_wr (by omega), lv_wr (by omega), lv_wr (by omega)]
  rw [this]

theorem nest4 (W a b c d Z : Nat) :
    a + W * (b + W * (c + W * (d + W * Z))) = a + W * b + W * W * c + W * W * W * d + W * W * W * W * Z := by
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- four limbs of `lshVU` -/
theorem lsh_step4 (X C Z0 Xl v0 v1 v2 v3 v4 j n s : Nat) (h1 : 1 ≤ s) (h2 : s ≤ 63)
    (b0 : v0 < 2 ^ 64) (b1 : v1 < 2 ^ 64) (b2 : v2 < 2 ^ 64) (b3 : v3 < 2 ^ 64)
    (hI : X * 2 ^ s = C * 2 ^ (64 * n) + 2 ^ (64 * (j + 5)) * Z0 + 2 ^ (64 * (j + 4)) * (v4 * 2 ^ s % 2 ^ 64) +
      (Xl + 2 ^ (64 * j) * v0 + 2 ^ (64 * (j + 1)) * v1 + 2 ^ (64 * (j + 2)) * v2 + 2 ^ (64 * (j + 3)) * v3) * 2 ^ s) :
    X * 2 ^ s = C * 2 ^ (64 * n) + 2 ^ (64 * (j + 1)) *
      ((v0 / 2 ^ (64 - s) + v1 * 2 ^ s % 2 ^ 64) + 2 ^ 64 * ((v1 / 2 ^ (64 - s) + v2 * 2 ^ s % 2 ^ 64) +
        2 ^ 64 * ((v2 / 2 ^ (64 - s) + v3 * 2 ^ s % 2 ^ 64) + 2 ^ 64 * ((v3 / 2 ^ (64 - s) + v4 * 2 ^ s % 2 ^ 64) +
          2 ^ 64 * Z0)))) + 2 ^ (64 * j) * (v0 * 2 ^ s % 2 ^ 64) + Xl * 2 ^ s := by
  have A := lsh_step X C Z0 (v4 * 2 ^ s % 2 ^ 64) (Xl + 2 ^ (64 * j) * v0 + 2 ^ (64 * (j + 1)) * v1 + 2 ^ (64 * (j + 2)) * v2)
    v3 (j + 3) n s b3 h1 h2 hI
  have B := lsh_step X C _ (v3 * 2 ^ s % 2 ^ 64) (Xl + 2 ^ (64 * j) * v0 + 2 ^ (64 * (j + 1)) * v1)
    v2 (j + 2) n s b2 h1 h2 A
  have Cc := lsh_step X C _ (v2 * 2 ^ s % 2 ^ 64) (Xl + 2 ^ (64 * j) * v0) v1 (j + 1) n s b1 h1 h2 B
  exact lsh_step X C _ (v1 * 2 ^ s % 2 ^ 64) Xl v0 j n s b0 h1 h2 Cc

theorem linv_step4 (m0 M : Memory) (x z n sh j t C w0 w1 w2 w3 : Nat) (h1 : 1 ≤ sh) (h2 : sh ≤ 63)
    (hI : LInv m0 M x z n sh (j + 4) t C)
    (hw0 : w0 % 2 ^ 64 = m0.readLE (x + 8 * j) 8 / 2 ^ (64 - sh) + m0.readLE (x + 8 * (j + 1)) 8 * 2 ^ sh % 2 ^ 64)
    (hw1 : w1 % 2 ^ 64 = m0.readLE (x + 8 * (j + 1)) 8 / 2 ^ (64 - sh) + m0.readLE (x + 8 * (j + 2)) 8 * 2 ^ sh % 2 ^ 64)
    (hw2 : w2 % 2 ^ 64 = m0.readLE (x + 8 * (j + 2)) 8 / 2 ^ (64 - sh) + m0.readLE (x + 8 * (j + 3)) 8 * 2 ^ sh % 2 ^ 64)
    (hw3 : w3 % 2 ^ 64 = m0.readLE (x + 8 * (j + 3)) 8 / 2 ^ (64 - sh) + m0.readLE (x + 8 * (j + 4)) 8 * 2 ^ sh % 2 ^ 64) :
    LInv m0 ((((M.writeLE (z + 8 * (j + 1)) 8 w0).writeLE (z + 8 * (j + 1) + 8) 8 w1).writeLE
      (z + 8 * (j + 1) + 16) 8 w2).writeLE (z + 8 * (j + 1) + 24) 8 w3) x z n sh j (t + 4) C := by
  unfold LInv at hI ⊢
  have l1 := lv_succ m0 x j
  have l2 := lv_succ m0 x (j + 1)
  have l3 := lv_succ m0 x (j + 2)
  have l4 := lv_succ m0 x (j + 3)
  rw [show j + 1 + 1 = j + 2 by omega] at l2
  rw [show j + 2 + 1 = j + 3 by omega] at l3
  rw [show j + 3 + 1 = j + 4 by omega] at l4
  rw [l4, l3, l2, l1] at hI
  have key := lsh_step4 (lv m0 x n) C (lv M (z + 8 * (j + 1 + 4)) t) (lv m0 x j) (m0.readLE (x + 8 * j) 8)
    (m0.readLE (x + 8 * (j + 1)) 8) (m0.readLE (x + 8 * (j + 2)) 8) (m0.readLE (x + 8 * (j + 3)) 8)
    (m0.readLE (x + 8 * (j + 4)) 8) j n sh h1 h2 (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) hI
  have hw := lv_w4 M (z + 8 * (j + 1)) t w0 w1 w2 w3
  rw [show 4 + t = t + 4 by omega] at hw
  rw [hw, show z + 8 * (j + 1) + 32 = z + 8 * (j + 1 + 4) by omega]
  rw [hw0, hw1, hw2, hw3]
  rw [nest4] at key
  have p1 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  have p2 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add, ← Nat.pow_add]
  have p3 : (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  rw [p1, p2, p3]
  exact key

/-- the invariant right after the first (top) word of a backward shift -/
theorem linv_init (m0 M : Memory) (x z m sh : Nat) (h1 : 1 ≤ sh) (h2 : sh ≤ 63) :
    LInv m0 M x z (m + 1) sh m 0 (m0.readLE (x + 8 * m) 8 / 2 ^ (64 - sh)) := by
  unfold LInv
  have e := shl_split (m0.readLE (x + 8 * m) 8) sh (limb_lt _ _) h1 h2
  generalize m0.readLE (x + 8 * m) 8 * 2 ^ sh % 2 ^ 64 = lo at e ⊢
  rw [lv_succ m0 x m, pow_succ64 m, lv_zero, Nat.mul_zero, Nat.add_zero, Nat.add_mul, Nat.mul_assoc, e]
  generalize 2 ^ (64 * m) = P
  generalize 2 ^ 64 = W
  generalize m0.readLE (x + 8 * m) 8 / 2 ^ (64 - sh) = hi
  generalize lv m0 x m * 2 ^ sh = Xl
  simp only [Nat.mul_add, Nat.add_mul]
  ac_rfl

end FvModexp.Asm
