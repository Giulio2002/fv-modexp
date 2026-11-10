import FvModexp.Proofs.Common.DivWW
import FvModexp.Proofs.Common.DivBasicMath
/-!
# The quotient-digit estimate of `divBasic` (natdiv.go:670-701)

```go
qhat := Word(_M)
if ujn != vn1 {
    var rhat Word
    qhat, rhat = divWW(ujn, u[j+n-1], vn1, rec)
    vn2 := v[n-2]
    x1, x2 := mulWW(qhat, vn2)
    ujn2 := u[j+n-2]
    for greaterThan(x1, x2, rhat, ujn2) {
        qhat--
        prevRhat := rhat
        rhat += vn1
        if rhat < prevRhat { break }
        x1, x2 = mulWW(qhat, vn2)
    }
}
```
* `greaterThan`  natdiv.go:726
* `corrLoop`     natdiv.go:684-696 (fuel = 2^64 is never exhausted: `qhat` decreases each round)
* `qhatEst`      natdiv.go:670-697
* `qhatEst_spec` the standard Knuth bound `X / D ≤ q̂ ≤ X / D + 1` for this estimate, plus `q̂ · (vn1·B + vn2) ≤ top three words of X`.
-/
namespace FvModexp.Mdl

/-- natdiv.go:726 `greaterThan(x1, x2, y1, y2)`. -/
def greaterThan (x1 x2 y1 y2 : Nat) : Prop := x1 > y1 ∨ (x1 = y1 ∧ x2 > y2)

instance (x1 x2 y1 y2 : Nat) : Decidable (greaterThan x1 x2 y1 y2) := by unfold greaterThan; infer_instance

/-- The `for greaterThan(x1, x2, rhat, ujn2) { ... }` loop (natdiv.go:684-696). `fuel` bounds the number of rounds. -/
def corrLoop (vn1 vn2 un2 : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, qhat, _, _, _ => qhat
  | fuel + 1, qhat, rhat, x1, x2 =>
    if greaterThan x1 x2 rhat un2 then
      let qhat' := (qhat + 2 ^ 64 - 1) % 2 ^ 64              -- qhat--
      let rhat' := (rhat + vn1) % 2 ^ 64                     -- rhat += vn1
      if rhat' < rhat then qhat'                              -- overflow: break
      else
        let p := mulWW qhat' vn2                              -- x1, x2 = mulWW(qhat, vn2)
        corrLoop vn1 vn2 un2 fuel qhat' rhat' p.1 p.2
    else qhat

/-- natdiv.go:670-697: the digit estimate. Arguments: `vn1 = v[n-1]`, `vn2 = v[n-2]`, `rec`, `ujn`, `u[j+n-1]`, `u[j+n-2]`. -/
def qhatEst (vn1 vn2 rec ujn un1 un2 : Nat) : Nat :=
  if ujn ≠ vn1 then
    let p := divWW ujn un1 vn1 rec
    let x := mulWW p.1 vn2
    corrLoop vn1 vn2 un2 (2 ^ 64) p.1 p.2 x.1 x.2
  else 2 ^ 64 - 1

theorem gt_iff (B x1 x2 y1 y2 : Nat) (hx2 : x2 < B) (hy2 : y2 < B) :
    greaterThan x1 x2 y1 y2 ↔ y1 * B + y2 < x1 * B + x2 := by
  unfold greaterThan
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · have : (y1 + 1) * B ≤ x1 * B := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul] at this; omega
    · subst h1; omega
  · intro h
    rcases Nat.lt_trichotomy x1 y1 with h1 | h1 | h1
    · have : (x1 + 1) * B ≤ y1 * B := Nat.mul_le_mul_right _ h1
      rw [Nat.add_mul] at this; omega
    · subst h1; right; omega
    · left; exact h1

theorem corrLoop_spec (vn1 vn2 un2 X2 : Nat) (hv2 : vn2 < 2 ^ 64) (hu : un2 < 2 ^ 64) :
    ∀ (fuel qhat rhat x1 x2 : Nat), qhat < 2 ^ 64 → rhat < 2 ^ 64 → vn1 < 2 ^ 64 → x1 * 2 ^ 64 + x2 = qhat * vn2 →
      x2 < 2 ^ 64 → rhat + qhat * vn1 = X2 → qhat + 1 ≤ fuel →
      corrLoop vn1 vn2 un2 fuel qhat rhat x1 x2 ≤ qhat ∧
      corrLoop vn1 vn2 un2 fuel qhat rhat x1 x2 * (vn1 * 2 ^ 64 + vn2) ≤ X2 * 2 ^ 64 + un2 ∧
      ∀ q', q' ≤ qhat → q' * (vn1 * 2 ^ 64 + vn2) ≤ X2 * 2 ^ 64 + un2 →
        q' ≤ corrLoop vn1 vn2 un2 fuel qhat rhat x1 x2
  := by
    intro fuel
    induction fuel with
    | zero => intros; omega
    | succ fuel ih =>
      intro qhat rhat x1 x2 hq hr hv1 hx hx2 hX2 hf
      have hB : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos 64
      have hmwS : ∀ x y, (mulWW x y).1 * 2 ^ 64 + (mulWW x y).2 = x * y := mulWW_spec
      have hmwB : ∀ x y, (mulWW x y).2 < 2 ^ 64 := fun x y => Nat.mod_lt _ hB
      unfold corrLoop
      generalize 2 ^ 64 = B at *
      have hexp : qhat * (vn1 * B + vn2) = (X2 * B + un2) - (rhat * B + un2) + qhat * vn2 := by
        have : X2 * B = rhat * B + qhat * vn1 * B := by rw [← hX2]; grind
        have h2 : qhat * (vn1 * B + vn2) = qhat * vn1 * B + qhat * vn2 := by grind
        omega
      have hgt := gt_iff B x1 x2 rhat un2 hx2 hu
      by_cases hc : greaterThan x1 x2 rhat un2
      · rw [if_pos hc]
        have hc' := hgt.1 hc
        -- qhat * V2 > X3
        have hbig : X2 * B + un2 < qhat * (vn1 * B + vn2) := by omega
        have hq1 : 1 ≤ qhat := by
          refine Nat.pos_of_ne_zero (fun h => ?_); subst h; simp at hbig
        have hqm : (qhat + B - 1) % B = qhat - 1 := by
          have : qhat + B - 1 = (qhat - 1) + B := by omega
          rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        simp only [hqm]
        by_cases hov : (rhat + vn1) % B < rhat
        · rw [if_pos hov]
          -- overflow: rhat + vn1 ≥ B
          have hov' : B ≤ rhat + vn1 := by
            refine Nat.le_of_not_lt (fun h => ?_)
            rw [Nat.mod_eq_of_lt h] at hov; omega
          have hlow : (qhat - 1) * (vn1 * B + vn2) ≤ X2 * B + un2 := by
            have e1 : (qhat - 1) * vn1 * B + B * B ≤ X2 * B := by
              have : X2 = rhat + qhat * vn1 := hX2.symm
              have e : qhat * vn1 = (qhat - 1) * vn1 + vn1 := by
                obtain ⟨t, rfl⟩ : ∃ t, qhat = t + 1 := ⟨qhat - 1, by omega⟩
                simp only [Nat.add_sub_cancel]; grind
              have : B ≤ X2 - (qhat - 1) * vn1 := by omega
              have h3 : (B) * B ≤ (X2 - (qhat - 1) * vn1) * B := Nat.mul_le_mul_right _ this
              have h4 : (qhat - 1) * vn1 ≤ X2 := by omega
              have h5 : (X2 - (qhat - 1) * vn1) * B = X2 * B - (qhat - 1) * vn1 * B := by
                rw [Nat.sub_mul]
              have h6 : (qhat - 1) * vn1 * B ≤ X2 * B := Nat.mul_le_mul_right _ h4
              omega
            have e2 : (qhat - 1) * vn2 < B * B := by
              have : (qhat - 1) * vn2 < B * B := Nat.mul_lt_mul'' (by omega) hv2
              exact this
            have e3 : (qhat - 1) * (vn1 * B + vn2) = (qhat - 1) * vn1 * B + (qhat - 1) * vn2 := by grind
            omega
          refine ⟨by omega, hlow, ?_⟩
          intro q' hq' hq'V
          refine Nat.le_of_not_lt (fun hlt => ?_)
          have : q' = qhat := by omega
          subst this; omega
        · rw [if_neg hov]
          have hmod : (rhat + vn1) % B = rhat + vn1 := by
            refine Nat.mod_eq_of_lt (Nat.lt_of_not_le (fun h => hov ?_))
            have : (rhat + vn1) % B = rhat + vn1 - B := by
              have : rhat + vn1 = (rhat + vn1 - B) + B := by omega
              conv => lhs; rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            omega
          have hlt : rhat + vn1 < B := by
            refine Nat.lt_of_not_le (fun h => hov ?_)
            have : (rhat + vn1) % B = rhat + vn1 - B := by
              have : rhat + vn1 = (rhat + vn1 - B) + B := by omega
              conv => lhs; rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            omega
          have hmw : (mulWW (qhat - 1) vn2).1 * B + (mulWW (qhat - 1) vn2).2 = (qhat - 1) * vn2 := hmwS _ _
          have hmw2 : (mulWW (qhat - 1) vn2).2 < B := hmwB _ _
          simp only [hmod]
          have ih := ih (qhat - 1) (rhat + vn1) (mulWW (qhat - 1) vn2).1
            (mulWW (qhat - 1) vn2).2 (by omega) hlt hv1 hmw hmw2
            (by
              have : qhat * vn1 = (qhat - 1) * vn1 + vn1 := by
                obtain ⟨t, rfl⟩ : ∃ t, qhat = t + 1 := ⟨qhat - 1, by omega⟩
                simp only [Nat.add_sub_cancel]; grind
              omega) (by omega)
          obtain ⟨i1, i2, i3⟩ := ih
          refine ⟨by omega, i2, ?_⟩
          intro q' hq' hq'V
          refine i3 q' ?_ hq'V
          refine Nat.le_of_not_lt (fun hlt' => ?_)
          have : q' = qhat := by omega
          subst this; omega
      · rw [if_neg hc]
        have hc' : ¬ (rhat * B + un2 < x1 * B + x2) := fun h => hc (hgt.2 h)
        have hrX : rhat * B ≤ X2 * B := Nat.mul_le_mul_right _ (by omega)
        refine ⟨Nat.le_refl _, by omega, fun q' hq' _ => hq'⟩


theorem hT_aux (B vn1 vn2 u0 N2 qq rr : Nat) (hdm : vn1 * qq + rr = N2) :
    qq * vn2 > rr * B + u0 ↔ N2 * B + u0 < qq * (vn1 * B + vn2) := by
  subst hdm
  have e1 : qq * (vn1 * B + vn2) = vn1 * qq * B + qq * vn2 := by grind
  have e3 : (vn1 * qq + rr) * B = vn1 * qq * B + rr * B := by grind
  generalize vn1 * qq * B = a at *
  generalize rr * B = b at *
  generalize qq * vn2 = c at *
  generalize (vn1 * qq + rr) * B = d at *
  generalize qq * (vn1 * B + vn2) = e at *
  omega

theorem qhatEst_spec (vn1 vn2 u2 u1 u0 β D X : Nat) (hv1 : 2 ^ 63 ≤ vn1) (hv1B : vn1 < 2 ^ 64) (hv2 : vn2 < 2 ^ 64)
    (hu0 : u0 < 2 ^ 64) (hu1 : u1 < 2 ^ 64) (hu2 : u2 ≤ vn1) (hβ : 0 < β)
    (hD1 : (vn1 * 2 ^ 64 + vn2) * β ≤ D) (hD2 : D < (vn1 * 2 ^ 64 + vn2 + 1) * β)
    (hX1 : ((u2 * 2 ^ 64 + u1) * 2 ^ 64 + u0) * β ≤ X) (hX2 : X < (((u2 * 2 ^ 64 + u1) * 2 ^ 64 + u0) + 1) * β)
    (hXD : X < 2 ^ 64 * D) :
    X / D ≤ qhatEst vn1 vn2 (reciprocalWord vn1) u2 u1 u0 ∧ qhatEst vn1 vn2 (reciprocalWord vn1) u2 u1 u0 ≤ X / D + 1 ∧
    qhatEst vn1 vn2 (reciprocalWord vn1) u2 u1 u0 < 2 ^ 64 ∧
    (u2 ≠ vn1 → qhatEst vn1 vn2 (reciprocalWord vn1) u2 u1 u0 * (vn1 * 2 ^ 64 + vn2) ≤ (u2 * 2 ^ 64 + u1) * 2 ^ 64 + u0) := by
  have hb := Knuth.qhat1_bounds (2 ^ 64) vn1 vn2 u2 u1 u0 β D X (by omega) hv1B hv2 hu0 hu1
    (by have : u2 < 2 ^ 64 := by omega
        exact this) hβ hD1 hD2 hX1 hX2 hXD
  by_cases he : u2 = vn1
  · subst he
    have h1 : Knuth.qhat1 (2 ^ 64) u2 vn2 u2 u1 u0 = 2 ^ 64 - 1 := by unfold Knuth.qhat1; simp
    have h2 : qhatEst u2 vn2 (reciprocalWord u2) u2 u1 u0 = 2 ^ 64 - 1 := by unfold qhatEst; simp
    rw [h1] at hb; rw [h2]
    refine ⟨hb.1, hb.2, by omega, fun h => absurd rfl h⟩
  · have hlt : u2 < vn1 := by omega
    have hvpos : 0 < vn1 := by omega
    have hrec := reciprocalWord_spec vn1 hvpos hv1B
    have hw := divWW_spec u2 u1 vn1 (reciprocalWord vn1) hvpos hv1B hlt hu1 hrec
    have hqe : qhatEst vn1 vn2 (reciprocalWord vn1) u2 u1 u0 = corrLoop vn1 vn2 u0 (2 ^ 64)
        ((u2 * 2 ^ 64 + u1) / vn1) ((u2 * 2 ^ 64 + u1) % vn1)
        (mulWW ((u2 * 2 ^ 64 + u1) / vn1) vn2).1 (mulWW ((u2 * 2 ^ 64 + u1) / vn1) vn2).2 := by
      unfold qhatEst; simp only [he, ne_eq, not_false_eq_true, ite_true, hw]
    rw [hqe]
    obtain ⟨N2, hN2⟩ : ∃ N2, N2 = u2 * 2 ^ 64 + u1 := ⟨_, rfl⟩
    rw [← hN2] at hX1 hX2 hqe ⊢
    have hdm := Nat.div_add_mod N2 vn1
    have hrl : N2 % vn1 < vn1 := Nat.mod_lt _ hvpos
    have hq0B : N2 / vn1 < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : N2 < (u2 + 1) * 2 ^ 64 := by rw [hN2, Nat.add_mul]; omega
      have h2 : (u2 + 1) * 2 ^ 64 ≤ vn1 * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      rw [Nat.mul_comm vn1]; omega
    have hmw := mulWW_spec (N2 / vn1) vn2
    have hmwB : (mulWW (N2 / vn1) vn2).2 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
    obtain ⟨c1, c2, c3⟩ := corrLoop_spec vn1 vn2 u0 N2 hv2 hu0 (2 ^ 64) (N2 / vn1) (N2 % vn1)
      (mulWW (N2 / vn1) vn2).1 (mulWW (N2 / vn1) vn2).2 hq0B (by omega) hv1B hmw hmwB (by have := Nat.mul_comm (N2 / vn1) vn1; omega) (by omega)
    generalize corrLoop vn1 vn2 u0 (2 ^ 64) (N2 / vn1) (N2 % vn1) (mulWW (N2 / vn1) vn2).1 (mulWW (N2 / vn1) vn2).2 = r at *
    -- relate to qhat1
    have hq1 : Knuth.qhat1 (2 ^ 64) vn1 vn2 u2 u1 u0 =
        if (N2 / vn1) * vn2 > (N2 % vn1) * 2 ^ 64 + u0 then N2 / vn1 - 1 else N2 / vn1 := by
      unfold Knuth.qhat1; rw [hN2]; simp only [show ¬ vn1 ≤ u2 by omega, ite_false]
    rw [hq1] at hb
    obtain ⟨hb1, hb2⟩ := hb
    -- q ≤ r
    have hqV : X / D * (vn1 * 2 ^ 64 + vn2) ≤ N2 * 2 ^ 64 + u0 := by
      have h1 : X / D * (vn1 * 2 ^ 64 + vn2) * β ≤ X / D * D := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hD1
      have h2 : X / D * D ≤ X := Nat.div_mul_le_self X D
      have h3 : X / D * (vn1 * 2 ^ 64 + vn2) * β < (N2 * 2 ^ 64 + u0 + 1) * β := Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) hX2
      have := Nat.lt_of_mul_lt_mul_right h3
      omega
    have hqle : X / D ≤ N2 / vn1 := by
      split at hb1 <;> omega
    have hqr : X / D ≤ r := c3 _ hqle hqV
    -- r ≤ qhat1
    have hT : (N2 / vn1) * vn2 > (N2 % vn1) * 2 ^ 64 + u0 ↔ N2 * 2 ^ 64 + u0 < (N2 / vn1) * (vn1 * 2 ^ 64 + vn2) :=
      hT_aux _ _ _ _ _ _ _ hdm
    have hrq : r ≤ N2 / vn1 - 1 ∨ ¬ ((N2 / vn1) * vn2 > (N2 % vn1) * 2 ^ 64 + u0) := by
      by_cases hc : (N2 / vn1) * vn2 > (N2 % vn1) * 2 ^ 64 + u0
      · left
        have := hT.1 hc
        refine Nat.le_of_not_lt (fun h => ?_)
        have : r = N2 / vn1 := by omega
        subst this; omega
      · right; exact hc
    refine ⟨hqr, ?_, by omega, fun _ => c2⟩
    split at hb2 <;> omega

end FvModexp.Mdl
