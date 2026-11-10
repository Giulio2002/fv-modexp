import FvModexp.Proofs.Common.ExpWindow
/-
  ExpSlow: nat.expNNSlow (nat.go:732-799), naive left-to-right square-and-multiply with `nat.div`
  reduction (m = 0: no reduction).  It is the window-size-1 instance of the shared loop skeleton.
-/
namespace FvModexp.Exp

/-- `expNNSlow(x, y, m)` (requires y > 1). `nat.sqr`, `nat.mul`, `nat.div` are `*`, `*`, `%`. -/
def expNNSlow (x y m : Nat) : Nat :=
  let step := fun z d =>
    let z1 := z * z                                  -- zz = zz.sqr(stk, z)
    let z2 := if d ≠ 0 then z1 * x else z1           -- if v&mask != 0 { zz = zz.mul(stk, z, x) }
    if m ≠ 0 then z2 % m else z2                     -- if len(m) != 0 { zz, r = zz.div(stk, r, z, m) }
  let i := nlen y - 1                                -- v := y[len(y)-1]
  let v := wd y i
  let shift := (64 - bitLen v) + 1                   -- shift := nlz(v) + 1
  -- z = x; v <<= shift; w = _W - shift iterations on the top word, then 64 per lower word
  outerLoop 1 step y 64 i (v * 2 ^ shift % B) (64 - shift) x

def SRep (m x z e : Nat) : Prop := (m = 0 → z = x ^ e) ∧ (0 < m → z % m = x ^ e % m)

theorem mulmod_congr {a b c d m : Nat} (h1 : a % m = b % m) (h2 : c % m = d % m) :
    a * c % m = b * d % m := by
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem expNNSlow_correct (x y m : Nat) (hy : 2 ≤ y) :
    expNNSlow x y m = if m = 0 then x ^ y else x ^ y % m := by
  unfold expNNSlow
  simp only
  obtain ⟨step, hstep⟩ : ∃ step : Nat → Nat → Nat, step = fun z d =>
      if m ≠ 0 then (if d ≠ 0 then z * z * x else z * z) % m
      else (if d ≠ 0 then z * z * x else z * z) := ⟨_, rfl⟩
  rw [← hstep]
  have hs : StepOk 1 (SRep m x) step := by
    intro z e d hd hz
    have hd' : d = 0 ∨ d = 1 := by simp at hd; omega
    have e2 : e * 2 ^ 1 = e + e := by omega
    have hsq : x ^ (e * 2 ^ 1 + 0) = x ^ e * x ^ e := by rw [e2, Nat.add_zero, Nat.pow_add]
    have hsx : x ^ (e * 2 ^ 1 + 1) = x ^ e * x ^ e * x := by rw [e2, Nat.pow_succ, Nat.pow_add]
    have sd0 : step z 0 = if m ≠ 0 then z * z % m else z * z := by rw [hstep]; simp
    have sd1 : step z 1 = if m ≠ 0 then z * z * x % m else z * z * x := by rw [hstep]; simp
    refine ⟨fun hm0 => ?_, fun hm0 => ?_⟩
    · have hz0 := hz.1 hm0
      rcases hd' with rfl | rfl
      · rw [sd0, if_neg (by simp [hm0]), hz0, hsq]
      · rw [sd1, if_neg (by simp [hm0]), hz0, hsx]
    · have hz0 := hz.2 hm0
      have hmne : m ≠ 0 := by omega
      have h1 := mulmod_congr hz0 hz0
      rcases hd' with rfl | rfl
      · rw [sd0, if_pos hmne, hsq, Nat.mod_mod]; exact h1
      · rw [sd1, if_pos hmne, hsx, Nat.mod_mod]; exact mulmod_congr h1 rfl
  -- initial state and exponent
  have hy0 : 0 < y := by omega
  obtain ⟨i, hi⟩ : ∃ i, i = nlen y - 1 := ⟨_, rfl⟩
  have hyn := nlen_pos hy0
  have hyB : y < B ^ (i + 1) := by
    have := lt_B_nlen y; rwa [show nlen y = i + 1 by omega] at this
  have hyge : B ^ i ≤ y := hi ▸ nlen_minimal hy0
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hv0 : 0 < wd y i := by
    unfold wd
    have h1 : 1 ≤ y / B ^ i := (Nat.le_div_iff_mul_le hBi).mpr (by omega)
    have h2 : y / B ^ i < B := by
      rw [Nat.div_lt_iff_lt_mul hBi, Nat.mul_comm]
      have h := hyB; rw [Nat.pow_succ] at h; exact h
    rw [Nat.mod_eq_of_lt h2]; omega
  have hexp : wd y i * B ^ i + y % B ^ i = y := by
    unfold wd
    have := Nat.mod_mul (a := B ^ i) (b := B) (x := y)
    rw [← Nat.pow_succ, Nat.mod_eq_of_lt hyB] at this
    grind
  obtain ⟨v, hv⟩ : ∃ v, v = wd y i := ⟨_, rfl⟩
  rw [← hi, ← hv]
  have hvB : v < B := hv ▸ wd_lt y i
  have hv0' : 0 < v := hv ▸ hv0
  obtain ⟨bl, hbl⟩ : ∃ bl, bl = bitLen v := ⟨_, rfl⟩
  have hbl1 : 1 ≤ bl := hbl ▸ bitLen_pos hv0'
  have hbl64 : bl ≤ 64 := hbl ▸ bitLen_le_of_lt (B_def ▸ hvB)
  have hvlt := bitLen_lt hv0'
  have hvge := bitLen_ge hv0'
  rw [← hbl] at hvlt hvge ⊢
  -- the loop
  have hrun := outerLoop_rep 1 (SRep m x) step (by omega) (by decide) hs y i
    (v * 2 ^ (64 - bl + 1) % B) (64 - (64 - bl + 1)) x 1 (by omega) (Nat.mod_lt _ B_pos)
    ⟨fun h => by simp, fun h => by simp⟩
  have hc : 64 - (64 - bl + 1) = bl - 1 := by omega
  rw [hc] at hrun ⊢
  have hsh : 64 - (bl - 1) * 1 = 64 - bl + 1 := by omega
  have hB2 : B = 2 ^ (bl - 1) * 2 ^ (64 - bl + 1) := by
    rw [B_def, ← Nat.pow_add]; congr 1; omega
  have e1 : v * 2 ^ (64 - bl + 1) % B / 2 ^ (64 - (bl - 1) * 1) = v % 2 ^ (bl - 1) := by
    rw [hsh, hB2, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hvT : v / 2 ^ (bl - 1) = 1 := by
    have h1 : v / 2 ^ (bl - 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have : 2 ^ bl = 2 * 2 ^ (bl - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      omega
    have h2 : 1 ≤ v / 2 ^ (bl - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
    omega
  have hev : (1 * 2 ^ ((bl - 1) * 1) + v * 2 ^ (64 - bl + 1) % B / 2 ^ (64 - (bl - 1) * 1)) = v := by
    rw [e1]
    have := Nat.div_add_mod v (2 ^ (bl - 1))
    rw [hvT] at this
    simp only [Nat.mul_one, Nat.one_mul]; omega
  rw [hev, hv, hexp] at hrun
  rw [← hv] at hrun
  simp only [Nat.div_one] at hrun
  have hcpos : 0 < i ∨ 0 < bl - 1 := by
    by_cases hi0 : i = 0
    · right
      refine Nat.pos_of_ne_zero (fun hbl0 => ?_)
      have h1 : bl = 1 := by omega
      rw [h1] at hvlt
      subst hi0
      have : wd y 0 = v := hv.symm
      rw [this] at hexp
      simp at hexp; omega
    · left; omega
  have hcpos' : 0 < i ∨ 0 < bl - 1 ∨ (0 < m → x < m) := by
    rcases hcpos with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hQ := outerLoop_Q 1 step (fun z => 0 < m → z < m) (by
      intro z d hm
      rw [hstep]
      dsimp only
      split
      · exact Nat.mod_lt _ hm
      · rename_i h; omega) y (by decide)
    i (v * 2 ^ (64 - bl + 1) % B) (bl - 1) x hcpos'
  by_cases hm0 : m = 0
  · rw [if_pos hm0]; exact hrun.1 hm0
  · have hm' : 0 < m := by omega
    rw [if_neg hm0, ← hrun.2 hm', Nat.mod_eq_of_lt (hQ hm')]

end FvModexp.Exp
