import FvModexp.Proofs.Common.ExpBase
/-
  ExpWindow: the common loop skeleton of expNNPowerOfTwoWindowSize{2,4} (nat.go:975-1127, 1129-1285),
  expNNOddMontgomeryWindowSize{2,4} (nat.go:1363-1494, 1496-1700) and expNNSlow (nat.go:732-799, w = 1),
  and its correctness for an abstract "representation" relation.

  Go shape (all four windowed routines):
      i := len(y)-1 ; yi := y[i] ; k := (bitLen(yi)+w-1)/w - 1
      z = table[yi >> (k*w)] ; yi <<= 64 - k*w ; k--
      for { for k >= 0 { z = step(z, table[yi >> (64-w)]) ; yi <<= w ; k-- }
            if i == 0 { break } ; i-- ; yi = y[i] ; k = 64/w - 1 }
-/
namespace FvModexp.Exp

/-- Inner loop `for k >= 0 { …; yi <<= w; k-- }` run `c` times (`c = k+1`). `step z d` consumes the window
`d = yi >> (64-w)`. -/
def wordLoop (w : Nat) (step : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, z => z
  | c + 1, yi, z => wordLoop w step c ((yi * 2 ^ w) % B) (step z (yi / 2 ^ (64 - w)))

/-- Outer loop: `if i == 0 {break}; i--; yi = y[i]; k = 64/w-1` (count `K = 64/w`). -/
def outerLoop (w : Nat) (step : Nat → Nat → Nat) (y K : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, yi, c, z => wordLoop w step c yi z
  | i + 1, yi, c, z => outerLoop w step y K i (wd y i) K (wordLoop w step c yi z)

/-- Loop entry: first window copied from the table, then `outerLoop`. -/
def winRun (w : Nat) (step : Nat → Nat → Nat) (tbl : Nat → Nat) (y i yi : Nat) : Nat :=
  let k := (bitLen yi + (w - 1)) / w - 1
  outerLoop w step y (64 / w) i ((yi * 2 ^ (64 - k * w)) % B) k (tbl (yi / 2 ^ (k * w)))

/-- `v` split at position `s + c*w`. -/
theorem split_lemma (P Q Wd d r : Nat) (hP : 0 < P) (hQ : 0 < Q) (hW : 0 < Wd) (hr : r < P * Q) :
    ((d * (P * Q) + r) * Wd) % (P * Q * Wd) = r * Wd ∧
    (d * (P * Q) + r) / P = d * Q + r / P ∧
    (r * Wd) / (P * Wd) = r / P := by
  refine ⟨?_, ?_, ?_⟩
  · have : (d * (P * Q) + r) * Wd = r * Wd + (P * Q * Wd) * d := by
      rw [Nat.add_mul]; rw [Nat.mul_comm (P*Q*Wd) d, Nat.mul_assoc, Nat.mul_assoc]
      rw [Nat.mul_comm d (P * (Q * Wd))]; grind
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right hr hW)
  · have : d * (P * Q) + r = r + (d * Q) * P := by grind
    rw [this, Nat.add_mul_div_right _ _ hP]; grind
  · exact Nat.mul_div_mul_right _ _ hW

section generic
variable (w : Nat) (x : Nat) (Rep : Nat → Nat → Prop) (step : Nat → Nat → Nat)

/-- `step` consumes one window: if `z` represents `x^e`, `step z d` represents `x^(e*2^w + d)`. -/
def StepOk : Prop := ∀ z e d, d < 2 ^ w → Rep z e → Rep (step z d) (e * 2 ^ w + d)

theorem wordLoop_rep (hw : 0 < w) (hs : StepOk w Rep step) :
    ∀ c v z e, c * w ≤ 64 → v < B → Rep z e →
      Rep (wordLoop w step c v z) (e * 2 ^ (c * w) + v / 2 ^ (64 - c * w)) := by
  intro c
  induction c with
  | zero =>
    intro v z e _ hv hz
    have : v / 2 ^ (64 - 0 * w) = 0 := by
      simp only [Nat.zero_mul, Nat.sub_zero]; exact Nat.div_eq_of_lt (B_def ▸ hv)
    rw [this]; simpa [wordLoop] using hz
  | succ c ih =>
    intro v z e hc hv hz
    have hw64 : w ≤ 64 := by
      have : w ≤ (c+1) * w := Nat.le_mul_of_pos_left w (by omega)
      omega
    obtain ⟨s, hs'⟩ : ∃ s, s = 64 - (c + 1) * w := ⟨_, rfl⟩
    have h64 : 64 = s + c * w + w := by
      have : (c+1) * w = c * w + w := by grind
      omega
    obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ s := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ (c * w) := ⟨_, rfl⟩
    obtain ⟨Wd, hWd⟩ : ∃ Wd, Wd = 2 ^ w := ⟨_, rfl⟩
    have hP0 : 0 < P := by rw [hP]; exact Nat.two_pow_pos _
    have hQ0 : 0 < Q := by rw [hQ]; exact Nat.two_pow_pos _
    have hW0 : 0 < Wd := by rw [hWd]; exact Nat.two_pow_pos _
    have hB : B = P * Q * Wd := by
      unfold B; rw [hP, hQ, hWd, ← Nat.pow_add, ← Nat.pow_add]; rw [← h64]
    obtain ⟨d, hd⟩ : ∃ d, d = v / (P * Q) := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = v % (P * Q) := ⟨_, rfl⟩
    have hv' : v = d * (P * Q) + r := by
      rw [hd, hr]; exact (Nat.div_add_mod' v (P*Q)).symm
    have hrlt : r < P * Q := by rw [hr]; exact Nat.mod_lt _ (Nat.mul_pos hP0 hQ0)
    have hdlt : d < Wd := by
      rw [hd, Nat.div_lt_iff_lt_mul (Nat.mul_pos hP0 hQ0)]
      rw [hB] at hv; grind
    obtain ⟨e1, e2, e3⟩ := split_lemma P Q Wd d r hP0 hQ0 hW0 hrlt
    have hdiv : v / 2 ^ (64 - w) = d := by
      have : 64 - w = s + c * w := by omega
      rw [this, Nat.pow_add, ← hP, ← hQ]; exact hd.symm
    have hv2 : (v * 2 ^ w) % B = r * Wd := by
      have : v * 2 ^ w = (d * (P * Q) + r) * Wd := by rw [← hv', ← hWd]
      rw [this, hB]; exact e1
    have hrW : r * Wd < B := by
      rw [hB]; exact Nat.mul_lt_mul_of_pos_right hrlt hW0
    have hcw : c * w ≤ 64 := by omega
    have := ih ((v * 2 ^ w) % B) (step z d) (e * 2 ^ w + d) hcw
      (by rw [hv2]; exact hrW) (by rw [hWd] at hdlt; exact hs z e d hdlt hz)
    have h1 : 64 - c * w = s + w := by omega
    have h2 : (r * Wd) / 2 ^ (s + w) = r / P := by
      rw [Nat.pow_add, ← hP, ← hWd]; exact e3
    have key : e * 2 ^ ((c + 1) * w) + v / 2 ^ (64 - (c + 1) * w)
        = (e * 2 ^ w + d) * 2 ^ (c * w) + ((v * 2 ^ w) % B) / 2 ^ (64 - c * w) := by
      rw [hv2, h1, h2, ← hs']
      have : 2 ^ ((c + 1) * w) = Q * Wd := by
        rw [hQ, hWd, ← Nat.pow_add]; congr 1; grind
      rw [this, ← hP, ← hQ, ← hWd]
      have hvP : v / P = d * Q + r / P := by rw [← e2, ← hv']
      rw [hvP]; grind
    rw [key]
    simp only [wordLoop]
    rw [hdiv]
    exact this

theorem outerLoop_rep (hw : 0 < w) (hK : (64 / w) * w = 64) (hs : StepOk w Rep step) (y : Nat) :
    ∀ i yi c z e, c * w ≤ 64 → yi < B → Rep z e →
      Rep (outerLoop w step y (64 / w) i yi c z)
        ((e * 2 ^ (c * w) + yi / 2 ^ (64 - c * w)) * B ^ i + y % B ^ i) := by
  intro i
  induction i with
  | zero =>
    intro yi c z e hc hyi hz
    have := wordLoop_rep w Rep step hw hs c yi z e hc hyi hz
    simp only [outerLoop, Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
    exact this
  | succ i ih =>
    intro yi c z e hc hyi hz
    have h1 := wordLoop_rep w Rep step hw hs c yi z e hc hyi hz
    have h2 := ih (wd y i) (64 / w) (wordLoop w step c yi z)
      (e * 2 ^ (c * w) + yi / 2 ^ (64 - c * w)) (by omega) (wd_lt y i) h1
    simp only [outerLoop]
    have e64 : 2 ^ (64 / w * w) = B := by rw [hK]; exact B_def.symm
    rw [e64, hK] at h2
    have hmod : y % B ^ (i + 1) = y % B ^ i + B ^ i * (y / B ^ i % B) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have e0 : 2 ^ (64 - 64) = 1 := rfl
    rw [e0, Nat.div_one] at h2
    have : ((e * 2 ^ (c * w) + yi / 2 ^ (64 - c * w)) * B + wd y i) * B ^ i + y % B ^ i
        = ((e * 2 ^ (c * w) + yi / 2 ^ (64 - c * w)) * B ^ (i + 1) + y % B ^ (i + 1)) := by
      rw [hmod, Nat.pow_succ]; unfold wd; grind
    rw [← this]; exact h2

/-- `winRun` computes `x^(yi * B^i + y % B^i)`. -/
theorem winRun_rep (hw : 0 < w) (hK : (64 / w) * w = 64) (hw64 : w ≤ 64) (hs : StepOk w Rep step)
    (tbl : Nat → Nat) (htbl : ∀ d, d < 2 ^ w → Rep (tbl d) d) (y i yi : Nat)
    (hyi0 : 0 < yi) (hyi : yi < B) :
    Rep (winRun w step tbl y i yi) (yi * B ^ i + y % B ^ i) := by
  unfold winRun
  simp only
  obtain ⟨k, hk⟩ : ∃ k, k = (bitLen yi + (w - 1)) / w - 1 := ⟨_, rfl⟩
  rw [← hk]
  have hbl := bitLen_lt hyi0
  have hbl64 : bitLen yi ≤ 64 := bitLen_le_of_lt (B_def ▸ hyi)
  have hblp := bitLen_pos hyi0
  -- k*w < bitLen yi ≤ (k+1)*w
  have hkk : k + 1 = (bitLen yi + (w - 1)) / w := by
    have h := Nat.div_add_mod (bitLen yi + (w - 1)) w
    have h' := Nat.mod_lt (bitLen yi + (w - 1)) hw
    have hq : 1 ≤ (bitLen yi + (w - 1)) / w := by
      refine Nat.one_le_iff_ne_zero.mpr (fun h0 => ?_)
      rw [h0] at h; omega
    omega
  have hk12 : bitLen yi ≤ (k + 1) * w ∧ k * w < bitLen yi := by
    have h := Nat.div_add_mod (bitLen yi + (w - 1)) w
    have h' := Nat.mod_lt (bitLen yi + (w - 1)) hw
    have e : (k + 1) * w = k * w + w := by grind
    have e2 : w * ((bitLen yi + (w - 1)) / w) = (k + 1) * w := by rw [hkk, Nat.mul_comm]
    omega
  have hk1 := hk12.1
  have hk2 := hk12.2
  have hkw : k * w ≤ 64 := by omega
  -- digit
  have hdig : yi / 2 ^ (k * w) < 2 ^ w := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    refine Nat.lt_of_lt_of_le hbl (Nat.pow_le_pow_right (by omega) ?_)
    have : (k + 1) * w = k * w + w := by grind
    omega
  have hz0 := htbl _ hdig
  have hyi' : (yi * 2 ^ (64 - k * w)) % B < B := Nat.mod_lt _ B_pos
  have := outerLoop_rep w Rep step hw hK hs y i ((yi * 2 ^ (64 - k * w)) % B) k (tbl (yi / 2 ^ (k * w)))
    (yi / 2 ^ (k * w)) hkw hyi' hz0
  have hBTU : B = 2 ^ (k * w) * 2 ^ (64 - k * w) := by
    unfold B; rw [← Nat.pow_add]; congr 1; omega
  have hmodeq : (yi * 2 ^ (64 - k * w)) % B / 2 ^ (64 - k * w) = yi % 2 ^ (k * w) := by
    rw [hBTU, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  rw [hmodeq] at this
  have hsum : (yi / 2 ^ (k * w) * 2 ^ (k * w) + yi % 2 ^ (k * w)) = yi := by
    have := Nat.div_add_mod yi (2 ^ (k * w))
    grind
  rw [hsum] at this
  exact this
end generic

end FvModexp.Exp
