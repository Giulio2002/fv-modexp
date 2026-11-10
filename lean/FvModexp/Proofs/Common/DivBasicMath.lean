/-!
# Pure Nat lemmas for Knuth algorithm D (adapted from fv-uint256)

Adapted from fv-uint256 `lean/Fv256/Proofs/Common/UtilB.lean` (`qhat1`, `qhat1_bounds`, `knuth_nb`, `knuth_borrow`) and
`KnuthMathB.lean` (`iter_core`); pure arithmetic, no machine model.
-/
namespace FvModexp.Mdl.Knuth


/-- Knuth's quotient-digit estimate with the single `qhat*dl > rhat*B + u0` correction used by `udivremKnuth`. -/
def qhat1 (B dh dl u2 u1 u0 : Nat) : Nat :=
  if dh ≤ u2 then B - 1
  else if (((u2 * B + u1) / dh) * dl > ((u2 * B + u1) % dh) * B + u0) then (u2 * B + u1) / dh - 1
  else (u2 * B + u1) / dh

theorem qhat1_bounds (B dh dl u2 u1 u0 β D X : Nat)
    (hdh2 : B ≤ 2 * dh) (hdhB : dh < B) (hdl : dl < B) (hu0 : u0 < B) (hu1 : u1 < B) (hu2 : u2 < B)
    (hβ : 0 < β)
    (hD1 : (dh * B + dl) * β ≤ D) (hD2 : D < (dh * B + dl + 1) * β)
    (hX1 : ((u2 * B + u1) * B + u0) * β ≤ X) (hX2 : X < (((u2 * B + u1) * B + u0) + 1) * β)
    (hXD : X < B * D) :
    X / D ≤ qhat1 B dh dl u2 u1 u0 ∧ qhat1 B dh dl u2 u1 u0 ≤ X / D + 1 := by
  have hD2pos : 0 < dh * B + dl := by
    have : 0 < dh := by omega
    have : 0 < B := by omega
    have := Nat.mul_pos ‹0 < dh› ‹0 < B›
    omega
  have hD0 : 0 < D := Nat.lt_of_lt_of_le (Nat.mul_pos hD2pos hβ) hD1
  have hdiv := Nat.div_add_mod X D
  have hmod := Nat.mod_lt X hD0
  obtain ⟨q, hq⟩ : ∃ q, q = X / D := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = X % D := ⟨_, rfl⟩
  rw [← hq, ← hr] at hdiv
  rw [← hr] at hmod
  rw [← hq]
  have hqB : q < B := by
    refine Nat.lt_of_mul_lt_mul_right (a := D) ?_
    have : q * D ≤ X := by rw [Nat.mul_comm q D]; omega
    omega
  have hqD : q * D ≤ X := by rw [Nat.mul_comm q D]; omega
  have hXq : X < (q + 1) * D := by rw [Nat.succ_mul, Nat.mul_comm q D]; omega
  unfold qhat1
  by_cases hA : dh ≤ u2
  · simp only [hA, ite_true]
    refine ⟨by omega, ?_⟩
    refine Nat.le_of_not_lt (fun hlt => ?_)
    -- q + 3 ≤ B
    have h1 : (q + 1) * D ≤ (B - 2) * D := Nat.mul_le_mul_right _ (by omega)
    have h2 : (B - 2) * D ≤ (B - 2) * ((dh * B + dl + 1) * β) := Nat.mul_le_mul_left _ (Nat.le_of_lt hD2)
    have h3 : dh * B ≤ u2 * B + u1 := by
      have := Nat.mul_le_mul_right B hA
      omega
    have h4 : dh * B * B * β ≤ ((u2 * B + u1) * B + u0) * β := Nat.mul_le_mul_right _ (by
      have := Nat.mul_le_mul_right B h3
      omega)
    have h5 : (dh * B + dl + 1) ≤ (dh + 1) * B := by
      have : (dh + 1) * B = dh * B + B := by grind
      omega
    have h6 : (B - 2) * ((dh * B + dl + 1) * β) ≤ (B - 2) * (((dh + 1) * B) * β) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h5)
    have h7 : dh * B * B * β < (B - 2) * (((dh + 1) * B) * β) := by omega
    have h8 : dh * B < (B - 2) * (dh + 1) := by
      have e1 : dh * B * B * β = (dh * B) * (B * β) := by grind
      have e2 : (B - 2) * (((dh + 1) * B) * β) = ((B - 2) * (dh + 1)) * (B * β) := by grind
      rw [e1, e2] at h7
      exact Nat.lt_of_mul_lt_mul_right h7
    have h9 : (B - 2) * (dh + 1) + 2 * (dh + 1) = B * (dh + 1) := by
      rw [← Nat.add_mul]; congr 1; omega
    have h10 : B * (dh + 1) = dh * B + B := by grind
    omega
  · simp only [hA, ite_false]
    have hu2 : u2 < dh := by omega
    obtain ⟨qh, hqh⟩ : ∃ qh, qh = (u2 * B + u1) / dh := ⟨_, rfl⟩
    obtain ⟨rh, hrh⟩ : ∃ rh, rh = (u2 * B + u1) % dh := ⟨_, rfl⟩
    have hN2 := Nat.div_add_mod (u2 * B + u1) dh
    rw [← hqh, ← hrh] at hN2
    have hrhd : rh < dh := by rw [hrh]; exact Nat.mod_lt _ (by omega)
    rw [← hqh, ← hrh]
    obtain ⟨N2, hN2d⟩ : ∃ N2, N2 = u2 * B + u1 := ⟨_, rfl⟩
    rw [← hN2d] at hN2 hX1 hX2
    obtain ⟨N3, hN3d⟩ : ∃ N3, N3 = N2 * B + u0 := ⟨_, rfl⟩
    rw [← hN3d] at hX1 hX2
    obtain ⟨D2, hD2d⟩ : ∃ D2, D2 = dh * B + dl := ⟨_, rfl⟩
    rw [← hD2d] at hD1 hD2 hD2pos
    have hi : q * D2 ≤ N3 := by
      have h1 : q * D2 * β ≤ q * D := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hD1
      have h2 : q * D2 * β < (N3 + 1) * β := by omega
      have := Nat.lt_of_mul_lt_mul_right h2
      omega
    have hiv : N3 < (q + 1) * (D2 + 1) := by
      have h1 : (q + 1) * D ≤ (q + 1) * ((D2 + 1) * β) := Nat.mul_le_mul_left _ (Nat.le_of_lt hD2)
      have h2 : N3 * β < ((q + 1) * (D2 + 1)) * β := by
        have e : (q + 1) * ((D2 + 1) * β) = ((q + 1) * (D2 + 1)) * β := by grind
        omega
      exact Nat.lt_of_mul_lt_mul_right h2
    have hD2gt : q < D2 := by
      have : dh * B ≤ D2 := by omega
      have : B * 1 ≤ dh * B := by
        have := Nat.mul_le_mul_right B (show 1 ≤ dh by omega)
        omega
      omega
    have hii : N3 < (qh + 1) * D2 := by
      have h1 : N3 < (N2 + 1) * B := by rw [hN3d, Nat.add_mul]; omega
      have h2 : (N2 + 1) * B ≤ (dh * qh + dh) * B := Nat.mul_le_mul_right _ (by omega)
      have h3 : (dh * qh + dh) * B = dh * B * (qh + 1) := by grind
      have h4 : dh * B * (qh + 1) ≤ D2 * (qh + 1) := Nat.mul_le_mul_right _ (by omega)
      have h5 : D2 * (qh + 1) = (qh + 1) * D2 := by grind
      omega
    have hv : qh ≤ q + 2 := by
      refine Nat.le_of_not_lt (fun hlt => ?_)
      have h1 : dh * (q + 3) ≤ dh * qh := Nat.mul_le_mul_left _ (by omega)
      have h2 : dh * B * (q + 3) ≤ N3 := by
        have : dh * (q + 3) ≤ N2 := by omega
        have := Nat.mul_le_mul_right B this
        have e : dh * B * (q + 3) = dh * (q + 3) * B := by grind
        omega
      have h3 : (q + 1) * (D2 + 1) ≤ (q + 1) * ((dh + 1) * B) := Nat.mul_le_mul_left _ (by
        have : (dh + 1) * B = dh * B + B := by grind
        omega)
      have h4 : dh * B * (q + 3) < (q + 1) * (dh + 1) * B := by
        have e : (q + 1) * ((dh + 1) * B) = (q + 1) * (dh + 1) * B := by grind
        omega
      have h5 : dh * (q + 3) < (q + 1) * (dh + 1) := by
        have e1 : dh * B * (q + 3) = dh * (q + 3) * B := by grind
        rw [e1] at h4
        exact Nat.lt_of_mul_lt_mul_right h4
      have h6 : (q + 1) * (dh + 1) = (q + 1) * dh + (q + 1) := by grind
      have h7 : dh * (q + 3) = dh * q + 3 * dh := by grind
      have h8 : (q + 1) * dh = q * dh + dh := by grind
      have h9 : dh * q = q * dh := by grind
      omega
    have hT : (qh * dl > rh * B + u0) ↔ N3 < qh * D2 := by
      have e1 : qh * D2 = qh * dh * B + qh * dl := by rw [hD2d]; grind
      have e2 : N3 = N2 * B + u0 := hN3d
      have e3 : N2 * B = (dh * qh + rh) * B := by rw [hN2]
      have e4 : (dh * qh + rh) * B = dh * qh * B + rh * B := by grind
      have e5 : dh * qh * B = qh * dh * B := by grind
      constructor <;> intro h <;> omega
    by_cases hTc : qh * dl > rh * B + u0
    · simp only [hTc, ite_true]
      have := hT.mp hTc
      refine ⟨?_, ?_⟩
      · have : q < qh := by
          refine Nat.lt_of_not_ge (fun hge => ?_)
          have := Nat.mul_le_mul_right D2 hge
          omega
        omega
      · omega
    · simp only [hTc, ite_false]
      have hn : ¬ N3 < qh * D2 := fun h => hTc (hT.mpr h)
      refine ⟨?_, ?_⟩
      · refine Nat.le_of_not_lt (fun hlt => ?_)
        have := Nat.mul_le_mul_right D2 (show qh + 1 ≤ q by omega)
        omega
      · refine Nat.le_of_not_lt (fun hlt => ?_)
        have : (q + 2) * D2 ≤ qh * D2 := Nat.mul_le_mul_right D2 (by omega)
        have e : (q + 2) * D2 = (q + 1) * D2 + D2 := by grind
        have e2 : (q + 1) * (D2 + 1) = (q + 1) * D2 + q + 1 := by grind
        omega

theorem knuth_nb (P D u2 Z qh q r b : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P)
    (hq1 : q * D ≤ u2 * P + Z) (hq2 : u2 * P + Z < (q + 1) * D)
    (hqh : q ≤ qh ∧ qh ≤ q + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) (hb : b ≤ u2) :
    qh = q ∧ b = u2 ∧ r = u2 * P + Z - q * D := by
  have e1 : (q + 1) * D = q * D + D := by grind
  obtain ⟨t, ht⟩ : ∃ t, u2 = b + t := ⟨u2 - b, by omega⟩
  have e2 : u2 * P = b * P + t * P := by rw [ht, Nat.add_mul]
  have hP : 0 < P := by omega
  rcases (show qh = q ∨ qh = q + 1 by omega) with h | h
  · subst h
    have : t = 0 := by
      refine Nat.eq_zero_of_not_pos (fun htp => ?_)
      have : P ≤ t * P := Nat.le_mul_of_pos_left P htp
      omega
    subst this
    refine ⟨rfl, by omega, by omega⟩
  · exfalso
    subst h
    have e3 : (q + 1) * D = q * D + D := e1
    have : 0 ≤ t * P := Nat.zero_le _
    omega

/-- Borrow case: the estimate was one too large; adding `D` back (dropping the carry out) repairs it. -/
theorem knuth_borrow (P D u2 Z qh q r b : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P)
    (hq1 : q * D ≤ u2 * P + Z) (hq2 : u2 * P + Z < (q + 1) * D)
    (hqh : q ≤ qh ∧ qh ≤ q + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) (hb : u2 < b) :
    qh = q + 1 ∧ b = u2 + 1 ∧ P ≤ r + D ∧ r + D - P = u2 * P + Z - q * D := by
  have e1 : (q + 1) * D = q * D + D := by grind
  obtain ⟨t, ht⟩ : ∃ t, b = u2 + 1 + t := ⟨b - u2 - 1, by omega⟩
  have e2 : b * P = u2 * P + P + t * P := by
    rw [ht, Nat.add_mul, Nat.add_mul, Nat.one_mul]
  have hP : 0 < P := by omega
  rcases (show qh = q ∨ qh = q + 1 by omega) with h | h
  · exfalso
    subst h
    have : 0 ≤ t * P := Nat.zero_le _
    omega
  · subst h
    have : t = 0 := by
      refine Nat.eq_zero_of_not_pos (fun htp => ?_)
      have : P ≤ t * P := Nat.le_mul_of_pos_left P htp
      omega
    subst this
    refine ⟨rfl, by omega, by omega, by omega⟩






theorem iter_core (P D X Z u2 qh b r : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P) (hX : X = u2 * P + Z)
    (hqh : X / D ≤ qh ∧ qh ≤ X / D + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) :
    (b ≤ u2 ∧ qh = X / D ∧ r = X % D) ∨
    (u2 < b ∧ qh = X / D + 1 ∧ P ≤ r + D ∧ r + D - P = X % D) := by
  have hdm := Nat.div_add_mod X D
  have hml : X % D < D := Nat.mod_lt _ hD0
  obtain ⟨q, hq⟩ : ∃ q, q = X / D := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = X % D := ⟨_, rfl⟩
  rw [← hq, ← hm] at hdm
  rw [← hm] at hml
  rw [← hq] at hqh
  rw [← hq, ← hm]
  have e0 : D * q = q * D := Nat.mul_comm _ _
  have e : (q + 1) * D = q * D + D := by grind
  have hq1 : q * D ≤ u2 * P + Z := by omega
  have hq2 : u2 * P + Z < (q + 1) * D := by omega
  rcases Nat.lt_or_ge u2 b with hb | hb
  · obtain ⟨h1, h2, h3, h4⟩ := knuth_borrow P D u2 Z qh q r b hD hD0 hZ hq1 hq2 hqh hsub hr hb
    right
    refine ⟨hb, h1, h3, ?_⟩
    omega
  · obtain ⟨h1, h2, h3⟩ := knuth_nb P D u2 Z qh q r b hD hD0 hZ hq1 hq2 hqh hsub hr hb
    left
    refine ⟨hb, h1, ?_⟩
    omega


end FvModexp.Mdl.Knuth
