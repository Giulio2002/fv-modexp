import FvModexp.Proofs.Common.DivBasic

/-!
# `divBasic`: model facts the machine-code proof needs (ISA independent)

* `ujn_le`: under the loop invariant, `ujn ≤ v[n-1]` (so `divWW(ujn, …, vn1)` has `ujn < vn1` when `ujn ≠ vn1`);
* `qhatEst_eq`: the model's estimate with `Mdl.divWW`/`Mdl.reciprocalWord` is the correction loop started from the true
  2-by-1 quotient and remainder (what the machine's `divWW` returns);
* `est_lt`: the estimate is a word.
-/

namespace FvModexp.Mdl

/-- the window facts at the start of iteration `j` (from the invariant with `j + 1` digits done) -/
theorem win_facts (v u0 q0 : List Nat) (m j : Nat) (q u : List Nat) (ujn : Nat)
    (hv : Wd v) (hn : 2 ≤ v.length) (hb : 2 ^ 63 ≤ topLimb v) (hu0 : Wd u0) (hmd : m + v.length = u0.length)
    (hjm : j ≤ m) (hI : DbInv v u0 q0 m (j + 1) q u ujn) :
    j + v.length ≤ u.length ∧ val (u.drop (j + v.length + 1)) = 0 ∧ val (u.drop j) < 2 ^ 64 * val v ∧
      ujn = u.getD (j + v.length) 0 ∧ 0 < val v := by
  obtain ⟨hWq, hWu, hql, hul, hut, huv, hujn, hqt, hqd, hqv⟩ := hI
  have hD0 : 0 < val v := by
    have := val_ge_top v
    have h2 : 0 < 2 ^ (64 * (v.length - 1)) := Nat.two_pow_pos _
    have : 0 < topLimb v * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (by omega) h2
    unfold topLimb at *; omega
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have F1 : u.getD j 0 = u0.getD j 0 := by
    rw [← getD_take_lt u j (j + 1) (by omega), hut, getD_take_lt _ _ _ (by omega)]
  have hY' : val (u.drop (j + 1)) = val (u0.drop (j + 1)) % val v := huv
  have hmodlt : val (u0.drop (j + 1)) % val v < val v := Nat.mod_lt _ hD0
  have hX : val (u.drop j) = u0.getD j 0 + 2 ^ 64 * (val (u0.drop (j + 1)) % val v) := by
    rw [val_drop_cons u j, F1, hY']
  have hXD : val (u.drop j) < 2 ^ 64 * val v := by
    have h1 : u0.getD j 0 < 2 ^ 64 := wd_getD hu0 _
    have h2 : 2 ^ 64 * (val (u0.drop (j + 1)) % val v + 1) ≤ 2 ^ 64 * val v := Nat.mul_le_mul_left _ hmodlt
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have hzero : val (u.drop (j + v.length + 1)) = 0 := by
    have h1 : val (u.drop (j + 1)) < 2 ^ (64 * v.length) := by rw [hY']; omega
    have := val_drop_zero (u.drop (j + 1)) v.length h1 (hWu.drop _)
    rw [List.drop_drop] at this
    have e : j + 1 + v.length = j + v.length + 1 := by omega
    rwa [e] at this
  have hujn' : ujn = u.getD (j + v.length) 0 := by
    have := hujn (by omega)
    rw [this]; congr 1
  exact ⟨by omega, hzero, hXD, hujn', hD0⟩

theorem ujn_le (v u : List Nat) (j ujn : Nat) (hv : Wd v) (hu : Wd u) (hn : 2 ≤ v.length)
    (hj : j + v.length ≤ u.length) (hzero : val (u.drop (j + v.length + 1)) = 0)
    (hXD : val (u.drop j) < 2 ^ 64 * val v) (hujn : ujn = u.getD (j + v.length) 0) : ujn ≤ topLimb v := by
  obtain ⟨k, hk⟩ : ∃ k, v.length = k + 2 := ⟨v.length - 2, by omega⟩
  have hL := (hu.drop j)
  have t1 := top3 (u.drop j) hL k (by simp; omega) (by
    rw [List.drop_drop]
    have : j + (k + 3) = j + v.length + 1 := by omega
    rw [this]; exact hzero)
  have t2 := top3 v hv k (by omega) (by rw [List.drop_eq_nil_of_le (by omega)]; rfl)
  have g1 : (u.drop j).getD (k + 2) 0 = ujn := by rw [getD_drop, hujn]; congr 1; omega
  have g4 : v.getD (k + 2) 0 = 0 := getD_out v _ (by omega)
  have g5 : v.getD (k + 1) 0 = topLimb v := by unfold topLimb; congr 1; omega
  rw [g1] at t1
  rw [g4, g5, Nat.zero_mul, Nat.zero_add] at t2
  have hvn2 : v.getD k 0 < 2 ^ 64 := wd_getD hv _
  exact top_le (2 ^ 64) _ _ _ _ _ _ _ _ hvn2 t2.2 t1.1 hXD

/-- the model's estimate = the correction loop from the true 2-by-1 division (for `ujn < vn1` when `ujn ≠ vn1`) -/
theorem qhatEst_eq (vn1 vn2 ujn un1 un2 : Nat) (hv1 : 2 ^ 63 ≤ vn1) (hv1B : vn1 < 2 ^ 64) (hle : ujn ≤ vn1)
    (hu1 : un1 < 2 ^ 64) :
    qhatEst vn1 vn2 (reciprocalWord vn1) ujn un1 un2 =
      if ujn ≠ vn1 then
        corrLoop vn1 vn2 un2 (2 ^ 64) ((ujn * 2 ^ 64 + un1) / vn1) ((ujn * 2 ^ 64 + un1) % vn1)
          ((ujn * 2 ^ 64 + un1) / vn1 * vn2 / 2 ^ 64) ((ujn * 2 ^ 64 + un1) / vn1 * vn2 % 2 ^ 64)
      else 2 ^ 64 - 1 := by
  unfold qhatEst
  by_cases h : ujn ≠ vn1
  · rw [if_pos h, if_pos h]
    rw [divWW_spec ujn un1 vn1 (reciprocalWord vn1) (by omega) hv1B (by omega) hu1
      (reciprocalWord_spec vn1 (by omega) hv1B)]
    rfl
  · rw [if_neg h, if_neg h]

end FvModexp.Mdl
