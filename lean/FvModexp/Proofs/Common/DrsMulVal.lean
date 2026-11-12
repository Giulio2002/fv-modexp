import FvModexp.Proofs.Common.DivBasicBridge
import FvModexp.Proofs.Common.DivRecIdeal
import FvModexp.Proofs.Common.MulClosed
import FvModexp.Proofs.Common.Conv

/-!
# `divRecursiveStep`: the value side of `qhat = qhat.norm()` and `qhatv = qhatv.mul(stk, qhat, v[:s])` (ISA independent)

* `normed_limbs`: a machine nat with `NatNorm` is a normalised limb list.
* `limbs_norm`: `qhat.norm()` in memory (`limbs t0 qn`, `NatNorm`, same value as `qhat[:B+1]`) is `Mdl.norm` of the model's `qhat`.
* `buf_mul`: the `qhatv` buffer after the product — `need` words holding the product, then zeros up to the buffer length —
  is the model's `p ++ replicate (N - |p|) 0` with `p = norm (toL v need)` (= `Mdl.mulI` of the operands), and the result
  length `l'` (`NatNorm`, value `v`) is `|p|` (`len_mul`).
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

open FvModexp.Mdl (Normed Wd val norm toL)

theorem normed_snoc : ∀ (l : List Nat) {d : Nat}, d ≠ 0 → Normed (l ++ [d])
  | [], d, h => Mdl.normed_cons.2 ⟨rfl, fun h' => h h'.2⟩
  | x :: xs, d, h => by
    rw [List.cons_append]
    exact Mdl.normed_cons.2 ⟨normed_snoc xs h, fun h' => by simp at h'⟩

/-- a machine nat with `NatNorm` is normalised -/
theorem normed_limbs {m : Memory} {p n : Nat} (h : NatNorm m p n) : Normed (limbs m p n) := by
  rcases n with _ | n
  · rfl
  · rw [limbs_succ_last]
    rcases h with h | h
    · omega
    · exact normed_snoc _ (by simpa using h)

/-- `qhat.norm()` in memory is the model's `norm qhat` -/
theorem limbs_norm {m : Memory} {p n k : Nat} {L : List Nat} (hL : limbs m p k = L)
    (hv : natVal m p n = natVal m p k) (hN : NatNorm m p n) : limbs m p n = norm L := by
  have hW : Wd L := hL ▸ Wd_limbs m p k
  refine Mdl.norm_unique _ _ (Wd_limbs m p n) (Mdl.Wd_norm hW) (normed_limbs hN) (Mdl.normed_norm _) ?_
  rw [Mdl.val_norm, ← hL, val_limbs, val_limbs]; exact hv

/-- the product buffer: `need` words holding `v`, then zeros, up to `N` words -/
theorem buf_mul {m : Memory} {p need N v : Nat} (hle : need ≤ N) (hv : natVal m p need = v)
    (hz : m.readLE (p + 8 * need) (8 * (N - need)) = 0) :
    limbs m p N = norm (toL v need) ++ List.replicate (N - (norm (toL v need)).length) 0 := by
  have hl := Mdl.length_norm_le (toL v need)
  rw [Mdl.length_toL] at hl
  have hvl : v < 2 ^ (64 * need) := by
    rw [← hv]; have := Memory.readLE_lt m p (8 * need)
    rwa [show (256 : Nat) ^ (8 * need) = 2 ^ (64 * need) by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega] at this
  refine eq_of_val (Wd_limbs m p N) (Mdl.Wd_append.2 ⟨Mdl.Wd_norm (Mdl.Wd_toL _ _), Mdl.Wd_replicate_zero _⟩)
    (by simp only [length_limbs, List.length_append, List.length_replicate]; omega) ?_
  rw [Mdl.val_append_zeros, Mdl.val_norm, Mdl.val_toL, Nat.mod_eq_of_lt hvl, val_limbs]
  unfold lv
  rw [show 8 * N = 8 * need + 8 * (N - need) by omega, Memory.readLE_add, hz]
  simp only [Nat.mul_zero, Nat.add_zero]; exact hv

/-- the result length of the product is the model's `|norm (toL v need)|` -/
theorem len_mul {m : Memory} {p l need v : Nat} (hv : natVal m p l = v) (hN : NatNorm m p l)
    (hvl : v < 2 ^ (64 * need)) : limbs m p l = norm (toL v need) := by
  refine Mdl.norm_unique _ _ (Wd_limbs m p l) (Mdl.Wd_norm (Mdl.Wd_toL _ _)) (normed_limbs hN) (Mdl.normed_norm _) ?_
  rw [Mdl.val_norm, Mdl.val_toL, Nat.mod_eq_of_lt hvl, val_limbs]; exact hv

/-- a suffix of a machine nat -/
theorem limbs_drop (m : Memory) : ∀ (p n k : Nat), (limbs m p n).drop k = limbs m (p + 8 * k) (n - k)
  | p, n, 0 => by simp
  | p, 0, k + 1 => by simp [limbs]
  | p, n + 1, k + 1 => by
    show (limbs m (p + 8) n).drop k = _
    rw [limbs_drop m (p + 8) n k, show p + 8 + 8 * k = p + 8 * (k + 1) by omega,
      show n + 1 - (k + 1) = n - k by omega]

end FvModexp.Asm
