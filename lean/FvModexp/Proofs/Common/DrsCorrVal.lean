import FvModexp.Proofs.Common.AsmModel

/-!
# Value models of the correction step's kernels (`subVW`, `addTo`): memory value form → `Mdl` limb lists

* `Mdl.addTo_mod`: `addTo(z, x)` (nat.go:234) is `z + x mod 2^(64·|z|)` (the carry out of `z` is dropped) — no
  no-overflow premise (cf. `addTo_spec`).
* `Asm.subVW_model`: the assembly summary's value/carry form of `subVW(z, x, y)` gives `Mdl.subVW`.
* `Asm.addTo_model`: `addTo`'s summary (`z' = (z + x) mod 2^(64 n)`) gives `Mdl.addTo`.
-/

set_option autoImplicit false

namespace FvModexp.Mdl

/-- `addTo(z, x)` (nat.go:234) = `(z + x) mod 2^(64·|z|)` -/
theorem addTo_mod (z x : List Nat) (hz : Wd z) (hx : Wd x) (hl : x.length ≤ z.length) :
    (addTo z x).length = z.length ∧ Wd (addTo z x) ∧
      val (addTo z x) = (val z + val x) % 2 ^ (64 * z.length) := by
  -- it suffices: `res + 2^(64 N) k = z + x` with `res` a word list of length `N`
  suffices h : (addTo z x).length = z.length ∧ Wd (addTo z x) ∧
      ∃ k, val (addTo z x) + 2 ^ (64 * z.length) * k = val z + val x by
    obtain ⟨h1, h2, k, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    have hlt := val_lt h2
    rw [h1] at hlt
    rw [← h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  unfold addTo
  simp only []
  by_cases hn : x.length = 0
  · rw [if_pos hn]
    have : x = [] := List.length_eq_zero_iff.1 hn
    subst this
    exact ⟨rfl, hz, 0, by simp⟩
  rw [if_neg hn]
  rw [List.take_length]
  have hlen : (z.take x.length).length = x.length := by simp; omega
  obtain ⟨i1, i2, i3, i4⟩ := addVVc_spec (z.take x.length) x 0 (hz.take _) hx hlen (by omega)
  have hzs := take_len_drop_val z x.length hl
  have hlo : (addVV (z.take x.length) x).1.length = x.length := by unfold addVV; rw [i1, hlen]
  have hsum : val (addVV (z.take x.length) x).1 + 2 ^ (64 * x.length) * (addVV (z.take x.length) x).2
      = val (z.take x.length) + val x := by
    unfold addVV; rw [hlen] at i4; omega
  have hwlo : Wd (addVV (z.take x.length) x).1 := i2
  have hc1' : (addVV (z.take x.length) x).2 ≤ 1 := i3
  have hdl : (z.drop x.length).length = z.length - x.length := by simp
  generalize (addVV (z.take x.length) x).1 = lo at *
  generalize (addVV (z.take x.length) x).2 = c at *
  have e2 : 2 ^ (64 * z.length) = 2 ^ (64 * x.length) * 2 ^ (64 * (z.length - x.length)) := by
    rw [← Nat.pow_add, ← Nat.mul_add]; congr 2; omega
  by_cases hc : c ≠ 0 ∧ x.length < z.length
  · rw [if_pos hc]
    obtain ⟨j1, j2, -, -, j5⟩ := addVW_spec (z.drop x.length) c (hz.drop _) (by omega)
    refine ⟨by rw [List.length_append, hlo, j1, hdl]; omega, Wd_append.2 ⟨hwlo, j2⟩, (addVW (z.drop x.length) c).2, ?_⟩
    rw [hdl] at j5
    rw [val_append, hlo, e2]
    have hP := congrArg (fun t => 2 ^ (64 * x.length) * t) j5
    simp only [Nat.mul_add] at hP
    rw [Nat.mul_assoc]
    omega
  · rw [if_neg hc]
    refine ⟨by simp [hlo, hdl]; omega, Wd_append.2 ⟨hwlo, hz.drop _⟩, ?_⟩
    rw [val_append, hlo]
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      exact ⟨0, by omega⟩
    · have hnz : x.length = z.length := by
        by_cases h : x.length < z.length
        · exact absurd ⟨by omega, h⟩ hc
        · omega
      have hd0 : z.drop x.length = [] := List.drop_eq_nil_of_le (by omega)
      have htk : z.take x.length = z := by rw [hnz]; exact List.take_length
      rw [htk] at hsum
      rw [hd0]
      refine ⟨c, ?_⟩
      rw [← hnz]; simp only [val, Nat.mul_zero, Nat.add_zero]; exact hsum

end FvModexp.Mdl

namespace FvModexp.Asm

open Janus Janus.Arm64

/-- `subVW` (assembly, value form: `Z = (X + 2^(64 n) − y) mod 2^(64 n)`, result word `n = 0 ? y : X < y`) agrees with
the model `Mdl.subVW` (arith.go:157) -/
theorem subVW_model (m m' : Memory) (z x n y r : Nat) (hy : y < 2 ^ 64)
    (hz : lv m' z n = (lv m x n + 2 ^ (64 * n) - y) % 2 ^ (64 * n))
    (hr : r = if n = 0 then y else if lv m x n < y then 1 else 0) :
    limbs m' z n = (Mdl.subVW (limbs m x n) y).1 ∧ r = (Mdl.subVW (limbs m x n) y).2 := by
  obtain ⟨hl, hw, hc1, hc0, hv⟩ := Mdl.subVW_spec (limbs m x n) y (Wd_limbs m x n) hy
  simp only [length_limbs, val_limbs] at hl hv
  have hlt := Mdl.val_lt hw
  rw [hl] at hlt
  have hZ := lv_lt m' z n
  have hX := lv_lt m x n
  by_cases hn : n = 0
  · subst hn
    have e0 : limbs m x 0 = [] := rfl
    rw [e0] at hc0 ⊢
    refine ⟨?_, by rw [hr, if_pos rfl, hc0 rfl]⟩
    show [] = _
    rw [show (Mdl.subVW [] y).1 = [] from rfl]
  have hne : limbs m x n ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
  have hc := hc1 hne
  have hP : 2 ^ 64 ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  generalize 2 ^ (64 * n) = P at *
  generalize (Mdl.subVW (limbs m x n) y).2 = c at *
  generalize hV : Mdl.val (Mdl.subVW (limbs m x n) y).1 = V at hv hlt
  have hc01 : c = 0 ∨ c = 1 := by omega
  have hcv : c = if lv m x n < y then 1 else 0 := by
    rcases hc01 with h | h <;> subst h <;> by_cases h' : lv m x n < y <;> simp only [h', if_true, if_false] <;> omega
  have hVe : V = (lv m x n + P - y) % P := by
    rcases hc01 with h | h
    · subst h
      rw [show lv m x n + P - y = V + P * 1 by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · subst h
      rw [show lv m x n + P - y = V by omega, Nat.mod_eq_of_lt hlt]
  refine ⟨eq_of_val (Wd_limbs m' z n) hw (by simp only [length_limbs]; exact hl.symm) ?_, ?_⟩
  · rw [val_limbs, hz, ← hVe, hV]
  · rw [hr, if_neg hn, hcv]

/-- `addTo` (assembly summary: `Z' = (Z + X) mod 2^(64 n)`, `l ≤ n`) agrees with the model `Mdl.addTo` (nat.go:234) -/
theorem addTo_model (m m' : Memory) (z x n l : Nat) (hl : l ≤ n)
    (hz : lv m' z n = (lv m z n + lv m x l) % 2 ^ (64 * n)) :
    limbs m' z n = Mdl.addTo (limbs m z n) (limbs m x l) := by
  obtain ⟨h1, h2, h3⟩ := Mdl.addTo_mod (limbs m z n) (limbs m x l) (Wd_limbs m z n) (Wd_limbs m x l)
    (by simp only [length_limbs]; exact hl)
  simp only [length_limbs, val_limbs] at h1 h3
  refine eq_of_val (Wd_limbs m' z n) h2 (by simp only [length_limbs]; exact h1.symm) ?_
  rw [val_limbs, hz, h3]

end FvModexp.Asm
