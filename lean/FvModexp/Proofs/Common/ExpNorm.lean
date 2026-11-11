import FvModexp.Proofs.Common.Conv

/-!
# `z.norm()` (nat.go:68-74) on memory: the normalised length of `p[0:l]`

`normL m p l` = the largest `l' ≤ l` such that the limbs `l'..l-1` are zero (`for i > 0 && z[i-1] == 0 { i-- }`).
-/

open Janus Janus.Arm64

namespace FvModexp.Expmc

def normL (m : Memory) (p : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => if m.readLE (p + 8 * l) 8 = 0 then normL m p l else l + 1

theorem normL_le (m : Memory) (p : Nat) : ∀ l, normL m p l ≤ l
  | 0 => Nat.le_refl _
  | l + 1 => by
    unfold normL; split
    · exact Nat.le_succ_of_le (normL_le m p l)
    · exact Nat.le_refl _

theorem normL_norm (m : Memory) (p : Nat) : ∀ l, NatNorm m p (normL m p l)
  | 0 => Or.inl rfl
  | l + 1 => by
    unfold normL; split
    · exact normL_norm m p l
    · rename_i h; exact Or.inr (by simpa using h)

theorem normL_val (m : Memory) (p : Nat) : ∀ l, m.readLE p (8 * normL m p l) = m.readLE p (8 * l)
  | 0 => rfl
  | l + 1 => by
    unfold normL; split
    · rename_i h
      rw [normL_val m p l, show 8 * (l + 1) = 8 * l + 8 by omega, Memory.readLE_add, h]; simp
    · rfl

end FvModexp.Expmc
