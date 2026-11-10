import FvModexp.Proofs.Common.DivBasicLemmas
import FvModexp.Proofs.Common.DivBasicEst
/-!
# `divBasic`: the digit estimate on a window of `u`

`est_facts`: for the window `u[j:]` with `ujn = u[j+n]`, the estimate `qhatEst` computed in natdiv.go:670-697 from
`ujn, u[j+n-1], u[j+n-2], v[n-1], v[n-2]` satisfies `X/D ≤ q̂ ≤ X/D + 1`, `q̂ < 2^64`, and when the window has only `n` limbs
(`j = m`, `ujn = 0` invented) `q̂ · D < 2^(64 n)` (so `qhatv[n] == 0`).
-/
namespace FvModexp.Mdl

theorem wd_getD {L : List Nat} (h : Wd L) (i : Nat) : L.getD i 0 < 2 ^ 64 := by
  by_cases hi : i < L.length
  · have : L.getD i 0 ∈ L := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ this
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ i)]

theorem getD_out (L : List Nat) (i : Nat) (h : L.length ≤ i) : L.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem Y_arith (a Y D X : Nat) (hD : 0 < D) (hX : X = a + 2 ^ 64 * (Y % D)) :
    (a + 2 ^ 64 * Y) % D = X % D ∧ (a + 2 ^ 64 * Y) / D = X / D + 2 ^ 64 * (Y / D) := by
  have hdm := Nat.div_add_mod Y D
  have e : a + 2 ^ 64 * Y = X + D * (2 ^ 64 * (Y / D)) := by
    have : 2 ^ 64 * Y = 2 ^ 64 * (D * (Y / D) + Y % D) := by rw [hdm]
    rw [hX, this, Nat.mul_add]
    have : 2 ^ 64 * (D * (Y / D)) = D * (2 ^ 64 * (Y / D)) := by grind
    omega
  rw [e]
  exact ⟨Nat.add_mul_mod_self_left _ _ _, Nat.add_mul_div_left _ _ hD⟩

theorem est_facts (v u : List Nat) (j ujn : Nat) (hv : Wd v) (hu : Wd u) (hn : 2 ≤ v.length) (hb : 2 ^ 63 ≤ topLimb v)
    (hj : j + v.length ≤ u.length) (hzero : val (u.drop (j + v.length + 1)) = 0)
    (hXD : val (u.drop j) < 2 ^ 64 * val v) (hujn : ujn = u.getD (j + v.length) 0) (qh : Nat)
    (hqe : qh = qhatEst (topLimb v) (v.getD (v.length - 2) 0) (reciprocalWord (topLimb v)) ujn
        (u.getD (j + v.length - 1) 0) (u.getD (j + v.length - 2) 0)) :
    val (u.drop j) / val v ≤ qh ∧ qh ≤ val (u.drop j) / val v + 1 ∧ qh < 2 ^ 64 ∧
    (u.length = j + v.length → qh * val v < 2 ^ (64 * v.length)) := by
  obtain ⟨k, hk⟩ : ∃ k, v.length = k + 2 := ⟨v.length - 2, by omega⟩
  -- three-limb windows
  have hL := (hu.drop j)
  have t1 := top3 (u.drop j) hL k (by simp; omega) (by
    rw [List.drop_drop]
    have : j + (k + 3) = j + v.length + 1 := by omega
    rw [this]; exact hzero)
  have t2 := top3 v hv k (by omega) (by rw [List.drop_eq_nil_of_le (by omega)]; rfl)
  have g1 : (u.drop j).getD (k + 2) 0 = ujn := by rw [getD_drop, hujn]; congr 1; omega
  have g2 : (u.drop j).getD (k + 1) 0 = u.getD (j + v.length - 1) 0 := by rw [getD_drop]; congr 1; omega
  have g3 : (u.drop j).getD k 0 = u.getD (j + v.length - 2) 0 := by rw [getD_drop]; congr 1; omega
  have g4 : v.getD (k + 2) 0 = 0 := getD_out v _ (by omega)
  have g5 : v.getD (k + 1) 0 = topLimb v := by unfold topLimb; congr 1; omega
  have g6 : v.getD k 0 = v.getD (v.length - 2) 0 := by congr 1; omega
  rw [g1, g2, g3] at t1
  rw [g4, g5, g6, Nat.zero_mul, Nat.zero_add] at t2
  have hvn1 : topLimb v < 2 ^ 64 := by unfold topLimb; exact wd_getD hv _
  have hvn2 : v.getD (v.length - 2) 0 < 2 ^ 64 := wd_getD hv _
  have hu1 : u.getD (j + v.length - 1) 0 < 2 ^ 64 := wd_getD hu _
  have hu0 : u.getD (j + v.length - 2) 0 < 2 ^ 64 := wd_getD hu _
  have hD0 : 0 < val v := by
    have := val_ge_top v
    have h2 : 0 < 2 ^ (64 * (v.length - 1)) := Nat.two_pow_pos _
    have : 0 < topLimb v * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (by omega) h2
    unfold topLimb at *; omega
  have hβ : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
  have hule : ujn ≤ topLimb v :=
    top_le (2 ^ 64) _ _ _ _ _ _ _ _ hvn2 t2.2 t1.1 hXD
  have hest := qhatEst_spec (topLimb v) (v.getD (v.length - 2) 0) ujn (u.getD (j + v.length - 1) 0)
    (u.getD (j + v.length - 2) 0) (2 ^ (64 * k)) (val v) (val (u.drop j)) hb hvn1 hvn2 hu0 hu1 hule hβ
    t2.1 t2.2 t1.1 t1.2 hXD
  obtain ⟨e1, e2, e3, e4⟩ := hest
  rw [← hqe] at e1 e2 e3 e4
  refine ⟨e1, e2, e3, ?_⟩
  intro hlen
  have hujn0 : ujn = 0 := by rw [hujn]; exact getD_out u _ (by omega)
  have hne : ujn ≠ topLimb v := by omega
  have e5 := e4 hne
  rw [hujn0] at e5
  have hq1 : qh ≤ 1 := by
    refine Nat.le_of_not_lt (fun h => ?_)
    have h2 : 2 * (topLimb v * 2 ^ 64) ≤ qh * (topLimb v * 2 ^ 64 + v.getD (v.length - 2) 0) := by
      have : 2 * (topLimb v * 2 ^ 64) ≤ qh * (topLimb v * 2 ^ 64) := Nat.mul_le_mul_right _ h
      have h3 : qh * (topLimb v * 2 ^ 64) ≤ qh * (topLimb v * 2 ^ 64 + v.getD (v.length - 2) 0) :=
        Nat.mul_le_mul_left _ (by omega)
      exact Nat.le_trans this h3
    have h4 : 2 ^ 64 * 2 ^ 64 ≤ 2 * (topLimb v * 2 ^ 64) := by
      have : 2 ^ 63 * 2 ^ 64 ≤ topLimb v * 2 ^ 64 := Nat.mul_le_mul_right _ hb
      have e : 2 * (2 ^ 63 * 2 ^ 64) = 2 ^ 64 * 2 ^ 64 := by decide
      omega
    have h5 : (0 * 2 ^ 64 + u.getD (j + v.length - 1) 0) * 2 ^ 64 + u.getD (j + v.length - 2) 0 < 2 ^ 64 * 2 ^ 64 := by
      have : u.getD (j + v.length - 1) 0 * 2 ^ 64 + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := by
        have := Nat.mul_le_mul_right (2 ^ 64) (show u.getD (j + v.length - 1) 0 + 1 ≤ 2 ^ 64 by omega)
        rw [Nat.add_mul] at this; omega
      rw [Nat.zero_mul, Nat.zero_add]; omega
    omega
  have hDlt := val_lt hv
  rcases Nat.lt_or_ge qh 1 with h0 | h1
  · have : qh = 0 := by omega
    rw [this, Nat.zero_mul]; exact Nat.two_pow_pos _
  · have : qh = 1 := by omega
    rw [this, Nat.one_mul]; exact hDlt

end FvModexp.Mdl
