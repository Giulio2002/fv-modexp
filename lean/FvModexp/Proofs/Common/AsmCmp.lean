import FvModexp.Proofs.Common.AsmLimbs

/-!
# Limb comparison from the top (the mathematics of `math/big.nat.cmp`, nat.go:152-180)

`top m p i n` is the value of the limbs `i+1 … n-1` at `p`. `nat.cmp` scans down from the top limb while the limbs agree;
the first differing limb (or limb 0) decides the comparison of the whole values (`lv_lt_of_top`, `lv_eq_of_top`).
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

/-- the value of the limbs `i+1 … n-1` at `p` -/
def top (m : Memory) (p i n : Nat) : Nat := m.readLE (p + 8 * (i + 1)) (8 * (n - (i + 1)))

theorem lv_split (m : Memory) (p i n : Nat) (h : i < n) :
    lv m p n = lv m p i + 2 ^ (64 * i) * m.readLE (p + 8 * i) 8 + 2 ^ (64 * (i + 1)) * top m p i n := by
  have e1 := lv_succ m p i
  unfold top
  unfold lv at e1 ⊢
  have e2 := Memory.readLE_add m p (8 * (i + 1)) (8 * (n - (i + 1)))
  rw [show 8 * (i + 1) + 8 * (n - (i + 1)) = 8 * n by omega, e1, pow256_eq] at e2
  exact e2

theorem top_last (m : Memory) (p n : Nat) (h : 0 < n) : top m p (n - 1) n = 0 := by
  unfold top; rw [show n - (n - 1 + 1) = 0 by omega]; simp [Memory.readLE]

theorem top_step (m : Memory) (p i n : Nat) (h : i + 1 < n) :
    top m p i n = m.readLE (p + 8 * (i + 1)) 8 + 2 ^ 64 * top m p (i + 1) n := by
  unfold top
  have e := Memory.readLE_add m (p + 8 * (i + 1)) 8 (8 * (n - (i + 1 + 1)))
  rw [show 8 + 8 * (n - (i + 1 + 1)) = 8 * (n - (i + 1)) by omega,
    show p + 8 * (i + 1) + 8 = p + 8 * (i + 1 + 1) by omega] at e
  rw [e]

/-- equal limbs above `i` and a smaller limb `i` give a smaller value -/
theorem lv_lt_of_top (m : Memory) (x y i n : Nat) (h : i < n) (ht : top m x i n = top m y i n)
    (hl : m.readLE (x + 8 * i) 8 < m.readLE (y + 8 * i) 8) : lv m x n < lv m y n := by
  rw [lv_split m x i n h, lv_split m y i n h, ht]
  have hx := lv_lt m x i
  have hm : 2 ^ (64 * i) * m.readLE (x + 8 * i) 8 + 2 ^ (64 * i) ≤ 2 ^ (64 * i) * m.readLE (y + 8 * i) 8 := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
  omega

/-- equal limbs `0 … n-1` give equal values -/
theorem lv_eq_of_top (m : Memory) (x y n : Nat) (h : 0 < n) (ht : top m x 0 n = top m y 0 n)
    (hl : m.readLE x 8 = m.readLE y 8) : lv m x n = lv m y n := by
  rw [lv_split m x 0 n h, lv_split m y 0 n h, ht]
  simp only [Nat.mul_zero, Nat.add_zero, lv_zero, hl]

end FvModexp.Asm
