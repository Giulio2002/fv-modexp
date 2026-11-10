import FvModexp.Proofs.Common.Conv

/-!
# Nat facts for the mul/div machine summaries (agent divmc)

ISA independent: limb values `natVal` split at a limb boundary, and the arithmetic that relates the
pieces a function writes (a low part from one call, a high part from another) to the value the summary
states.
-/

namespace FvModexp

open Janus Janus.Arm64

/-- Limbs split at limb `n`: the first `n` limbs are the low part. -/
theorem natVal_add (m : Memory) (p n k : Nat) :
    natVal m p (n + k) = natVal m p n + 2 ^ (64 * n) * natVal m (p + 8 * n) k := by
  unfold natVal
  rw [show 8 * (n + k) = 8 * n + 8 * k by omega, Memory.readLE_add]
  congr 2
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

theorem two_pow_64_add (n k : Nat) : 2 ^ (64 * (n + k)) = 2 ^ (64 * n) * 2 ^ (64 * k) := by
  rw [Nat.mul_add, Nat.pow_add]

/-- The value of a two-piece result: a low part `(a % B^n)` and a high part `(h + a / B^n) % B^k`
make `(a + B^n h) % B^(n+k)`. -/
theorem split_mod (a h n k : Nat) :
    a % 2 ^ (64 * n) + 2 ^ (64 * n) * ((h + a / 2 ^ (64 * n)) % 2 ^ (64 * k)) =
      (a + 2 ^ (64 * n) * h) % 2 ^ (64 * (n + k)) := by
  rw [two_pow_64_add, Nat.mod_mul]
  have hp : 0 < 2 ^ (64 * n) := Nat.pow_pos (by omega)
  congr 1
  · rw [Nat.add_mul_mod_self_left]
  · congr 2
    rw [Nat.mul_comm (2 ^ (64 * n)) h, Nat.add_mul_div_right _ _ hp, Nat.add_comm]

/-- `(a + B^n h) % B^n = a % B^n` style: a value below `B^n` is its own residue. -/
theorem mod_self_lt {a n : Nat} (h : a < 2 ^ (64 * n)) : a % 2 ^ (64 * n) = a := Nat.mod_eq_of_lt h

/-- One row of the schoolbook product (`basicMul`'s iteration `i`): the window `z[i : i + n]` (value `W`) receives
`W + X·d` with carry `c` into limb `i + n` (which was `0`), the low `i` limbs (value `Lo`) unchanged. -/
theorem bm_row (Lo W W' X Y d c i n : Nat)
    (hrow : W' + 2 ^ (64 * n) * c = W + X * d)
    (hinv : Lo + 2 ^ (64 * i) * W = X * Y) :
    Lo + 2 ^ (64 * i) * (W' + 2 ^ (64 * n) * c) = X * (Y + 2 ^ (64 * i) * d) := by
  rw [hrow, Nat.mul_add, ← Nat.add_assoc, hinv, Nat.mul_add, Nat.mul_left_comm]

end FvModexp
