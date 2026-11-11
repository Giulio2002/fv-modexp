import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Common.Slices

/-!
# Limb lists of memory under stores and window writes (ISA independent; for the `divBasic` machine proofs)

`Asm.limbs m p n` is the slice `p[0:n]` as the model's list. A write confined to the words `[j, j+k)` of the slice
is the model's `upd … j (new words)`; a sub-slice is the model's `sl`.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

theorem limbs_getElem (m : Memory) (p : Nat) : ∀ (n i : Nat) (h : i < (limbs m p n).length),
    (limbs m p n)[i] = m.readLE (p + 8 * i) 8
  | 0, i, h => by simp at h
  | n + 1, 0, _ => by simp [limbs]
  | n + 1, i + 1, h => by
    simp only [limbs, List.getElem_cons_succ]
    rw [limbs_getElem m (p + 8) n i (by simp at h ⊢; omega)]
    congr 1; omega

theorem limbs_getD (m : Memory) (p n i : Nat) (h : i < n) : (limbs m p n).getD i 0 = m.readLE (p + 8 * i) 8 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  simp only [Option.getD_some]
  exact limbs_getElem m p n i _

theorem limbs_ext {m m' : Memory} {p p' n : Nat} (h : ∀ i < n, m'.readLE (p' + 8 * i) 8 = m.readLE (p + 8 * i) 8) :
    limbs m' p' n = limbs m p n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [limbs_getElem, limbs_getElem]
  exact h i (by simpa using h1)

/-- a sub-slice -/
theorem sl_limbs (m : Memory) (p n j k : Nat) (h : j + k ≤ n) : Mdl.sl (limbs m p n) j k = limbs m (p + 8 * j) k := by
  apply List.ext_getElem
  · rw [Mdl.length_sl _ _ _ (by simpa using h)]; simp
  intro i h1 h2
  simp only [Mdl.sl, List.getElem_take, List.getElem_drop]
  rw [limbs_getElem, limbs_getElem]
  congr 1; omega

/-- a write confined to the words `[j, j + k)` -/
theorem limbs_upd {m m' : Memory} {p n j k : Nat} (h : j + k ≤ n)
    (hout : ∀ i < n, (i < j ∨ j + k ≤ i) → m'.readLE (p + 8 * i) 8 = m.readLE (p + 8 * i) 8) :
    limbs m' p n = Mdl.upd (limbs m p n) j (limbs m' (p + 8 * j) k) := by
  apply List.ext_getElem
  · rw [Mdl.upd_length' _ _ _ (by simp; omega)]; simp
  intro i h1 h2
  rw [limbs_getElem]
  simp only [length_limbs] at h1
  unfold Mdl.upd at h2 ⊢
  by_cases hi : i < j
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_take, limbs_getElem, hout i h1 (Or.inl hi)]
  · by_cases hi2 : i < j + k
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_take, length_limbs]
      rw [limbs_getElem]
      congr 1; simp only [List.length_take, length_limbs, List.length_append] at *; omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_take, length_limbs, List.getElem_drop]
      rw [limbs_getElem, hout i h1 (Or.inr (by omega))]
      congr 1; simp only [List.length_take, length_limbs, List.length_append] at *; omega

/-- one word -/
theorem limbs_one (m : Memory) (a : Nat) : limbs m a 1 = [m.readLE a 8] := by simp [limbs]

end FvModexp.Asm
