import FvModexp.Proofs.Common.DivLarge
import FvModexp.Proofs.Common.DivW
import FvModexp.Proofs.Common.NatBasic
/-!
# `nat.divW`, `nat.modW`, `nat.div`, `nat.rem` (natdiv.go:505-567) and `divWVW` correctness

* `divWVW_spec`   natdiv.go:572-584 (both the `len(x) == 1` `bits.Div` branch and the reciprocal loop)
* `natDivW`       natdiv.go:550-567 `(z nat) divW(x nat, y Word) (q nat, r Word)`
* `natModW`       natdiv.go:570 `(x nat) modW(d Word) (r Word)`
* `natDiv dr qs u v`  natdiv.go:518-545 `(z nat) div(stk, z2, u, v) (q, r)`
* `natRem dr qs u v`  natdiv.go:505-513 `(z nat) rem(stk, u, v) (r nat)`

`dr` = model of `divRecursive` (contract `DivRecursiveContract`).  `qs` = contents of the quotient storage `z.make(m+1)` that `divLarge` writes
into (arbitrary; all digits are overwritten).  For `rem` the quotient storage is `stk.nat(max(1, len(u)-(len(v)-1)))`, i.e. exactly
`m+1` words when `len u ≥ len v`.  Panics (division by zero) are theorem preconditions (`v ≠ []`, `y ≠ 0`).
-/
namespace FvModexp.Mdl

theorem Wd_reverse {l : List Nat} (h : Wd l) : Wd l.reverse := fun d hd => h d (List.mem_reverse.1 hd)

/-- `divWVW(z, xn, x, y)` for `len x ≥ 1`, `xn < y`: `z` has `len x` words, `xn * B^len + x = y * z + r`, `r < y`. -/
theorem divWVW_spec (xn : Nat) (x : List Nat) (y : Nat) (hx : Wd x) (hxne : x ≠ []) (hy : 0 < y) (hyB : y < 2 ^ 64)
    (hxn : xn < y) :
    (divWVW xn x y).1.length = x.length ∧ Wd (divWVW xn x y).1 ∧ (divWVW xn x y).2 < y ∧
    xn * 2 ^ (64 * x.length) + val x = y * val (divWVW xn x y).1 + (divWVW xn x y).2 := by
  unfold divWVW
  by_cases h1 : x.length = 1
  · rw [if_pos h1]
    obtain ⟨x0, rfl⟩ : ∃ x0, x = [x0] := by
      match x, h1 with
      | [a], _ => exact ⟨a, rfl⟩
    have hx0 : x0 < 2 ^ 64 := hx x0 (by simp)
    have := div64_spec xn x0 y hy hyB hx0 hxn
    simp only [List.getD_cons_zero, this]
    have hdm := Nat.div_add_mod (xn * 2 ^ 64 + x0) y
    have hq : (xn * 2 ^ 64 + x0) / y < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (xn + 1) * 2 ^ 64 ≤ y * 2 ^ 64 := Nat.mul_le_mul_right _ hxn
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm y]; omega
    refine ⟨rfl, Wd_cons.2 ⟨hq, Wd_nil⟩, Nat.mod_lt _ hy, ?_⟩
    simp only [List.length_cons, List.length_nil, val_cons, val_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
    omega
  · rw [if_neg h1]
    obtain ⟨i1, i2, i3, i4⟩ := divWVWLoop_spec y hy hyB x.reverse xn (Wd_reverse hx) hxn
    simp only [List.length_reverse] at i1 i4
    refine ⟨by simp [i1], Wd_reverse i2, i3, ?_⟩
    rw [val_reverse, ← i4]
    have := val_reverse x.reverse
    rw [List.reverse_reverse] at this
    rw [this]

/-- `nat.divW` (natdiv.go:550-567). `y == 0` panics (precondition). -/
def natDivW (x : List Nat) (y : Nat) : List Nat × Nat :=
  if y = 1 then (x, 0)                                   -- q = z.set(x)
  else if x.length = 0 then ([], 0)                      -- q = z[:0]
  else
    let t := divWVW 0 x y                                -- z = z.make(m); r = divWVW(z, 0, x, y)
    (norm t.1, t.2)                                      -- q = z.norm()

theorem natDivW_spec (x : List Nat) (y : Nat) (hx : Wd x) (hnx : Normed x) (hy : 0 < y) (hyB : y < 2 ^ 64) :
    Wd (natDivW x y).1 ∧ Normed (natDivW x y).1 ∧ val (natDivW x y).1 = val x / y ∧
    (natDivW x y).2 = val x % y ∧ (natDivW x y).1.length ≤ x.length := by
  unfold natDivW
  by_cases h1 : y = 1
  · rw [if_pos h1]; subst h1
    exact ⟨hx, hnx, by simp, by simp [Nat.mod_one], Nat.le_refl _⟩
  rw [if_neg h1]
  by_cases h0 : x.length = 0
  · rw [if_pos h0]
    have : x = [] := List.length_eq_zero_iff.1 h0
    subst this
    exact ⟨Wd_nil, rfl, by simp, by simp, Nat.le_refl _⟩
  rw [if_neg h0]
  have hxne : x ≠ [] := fun h => h0 (by rw [h]; rfl)
  obtain ⟨i1, i2, i3, i4⟩ := divWVW_spec 0 x y hx hxne hy hyB hy
  simp only [Nat.zero_mul, Nat.zero_add] at i4
  have hdm := Nat.div_mod_unique (a := val x) (b := y) (d := val (divWVW 0 x y).1) (c := (divWVW 0 x y).2) hy
  obtain ⟨hq, hr⟩ := (hdm).2 ⟨by omega, i3⟩
  refine ⟨Wd_norm i2, normed_norm _, by rw [val_norm, hq], hr.symm, ?_⟩
  exact Nat.le_trans (length_norm_le _) (by omega)

/-- `nat.modW` (natdiv.go:570-575): `x % d`. -/
def natModW (x : List Nat) (d : Nat) : Nat := (divWVW 0 x d).2

theorem natModW_spec (x : List Nat) (d : Nat) (hx : Wd x) (hd : 0 < d) (hdB : d < 2 ^ 64) :
    natModW x d = val x % d := by
  unfold natModW
  by_cases hxe : x = []
  · subst hxe; simp [divWVW, divWVWLoop]
  obtain ⟨i1, i2, i3, i4⟩ := divWVW_spec 0 x d hx hxe hd hdB hd
  simp only [Nat.zero_mul, Nat.zero_add] at i4
  have := (Nat.div_mod_unique (a := val x) (b := d) (d := val (divWVW 0 x d).1) (c := (divWVW 0 x d).2) hd).2
    ⟨by omega, i3⟩
  exact this.2.symm

/-- `nat.div` (natdiv.go:518-545): returns `(q, r)`; `len v = 0` panics (precondition `v ≠ []`). -/
def natDiv (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs u v : List Nat) :
    List Nat × List Nat :=
  if v.length = 1 then
    let p := natDivW u (v.getD 0 0)                      -- q, r2 = z.divW(u, v[0])
    (p.1, natSetWord p.2)                                -- r = z2.setWord(r2)
  else if natCmp u v < 0 then ([], u)                    -- q = z[:0]; r = z2.set(u)
  else divLarge dr qs u v                                -- z.divLarge(stk, z2, u, v)

theorem natSetWord_len (x : Nat) : (natSetWord x).length ≤ 1 := by
  unfold natSetWord; split <;> simp

theorem cmpInt_neg_iff (a b : Nat) : cmpInt a b < 0 ↔ a < b := by
  unfold cmpInt
  by_cases h : a < b
  · simp [h]
  · by_cases h2 : b < a <;> simp [h, h2] <;> omega

/-- `nat.div`: `q = ⌊u/v⌋`, `r = u % v`, both `Wd` and normalised, with the length bounds `len q ≤ len u - len v + 1`, `len r ≤ len v`.
Inputs: `u`, `v` `Wd` and normalised, `v ≠ []`; the quotient storage `qs` of the `divLarge` path has `m+1` words. -/
theorem natDiv_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs u v : List Nat) (hu : Wd u) (hv : Wd v) (hnu : Normed u) (hnv : Normed v) (hve : v ≠ [])
    (hqs : Wd qs) (hqsl : 2 ≤ v.length → v.length ≤ u.length → qs.length = u.length - v.length + 1) :
    Wd (natDiv dr qs u v).1 ∧ Wd (natDiv dr qs u v).2 ∧ Normed (natDiv dr qs u v).1 ∧ Normed (natDiv dr qs u v).2 ∧
    val (natDiv dr qs u v).1 = val u / val v ∧ val (natDiv dr qs u v).2 = val u % val v ∧
    (natDiv dr qs u v).1.length ≤ u.length - v.length + 1 ∧ (natDiv dr qs u v).2.length ≤ v.length := by
  have hvlen : 0 < v.length := List.length_pos_iff.2 hve
  unfold natDiv
  by_cases h1 : v.length = 1
  · rw [if_pos h1]
    obtain ⟨v0, rfl⟩ : ∃ v0, v = [v0] := by
      match v, h1 with
      | [a], _ => exact ⟨a, rfl⟩
    have hv0 : v0 < 2 ^ 64 := hv v0 (by simp)
    have hv00 : v0 ≠ 0 := by
      have := hnv.top_ne hve; simpa using this
    have := natDivW_spec u v0 hu hnu (by omega) hv0
    obtain ⟨d1, d2, d3, d4, d5⟩ := this
    have hmod : val u % v0 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by omega)) hv0
    obtain ⟨w1, w2, w3⟩ := natSetWord_spec (natDivW u (List.getD [v0] 0 0)).2 (by simp only [List.getD_cons_zero]; rw [d4]; exact hmod)
    simp only [List.getD_cons_zero] at *
    refine ⟨d1, w2, d2, w3, by simpa using d3, by rw [w1, d4]; simp, by simp only [List.length_cons, List.length_nil]; omega,
      Nat.le_trans (natSetWord_len _) (by simp)⟩
  · rw [if_neg h1]
    have h2 : 2 ≤ v.length := by omega
    rw [natCmp_spec u v hu hv hnu hnv]
    by_cases hlt : cmpInt (val u) (val v) < 0
    · rw [if_pos hlt]
      have hlt' := (cmpInt_neg_iff _ _).1 hlt
      refine ⟨Wd_nil, hu, rfl, hnu, by simp [Nat.div_eq_of_lt hlt'], by simp [Nat.mod_eq_of_lt hlt'], by simp, ?_⟩
      exact normed_len_le hnu hu _ (Nat.lt_trans hlt' (val_lt hv))
    · rw [if_neg hlt]
      have hge : ¬ val u < val v := fun h => hlt ((cmpInt_neg_iff _ _).2 h)
      have hle : v.length ≤ u.length := by
        refine Nat.le_of_not_lt (fun h => hge ?_)
        have e1 := val_lt hu
        have e2 := hnv.val_ge hve hv
        have : 2 ^ (64 * u.length) ≤ 2 ^ (64 * (v.length - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := divLarge_spec dr hdr qs u v hqs (hqsl h2 hle) hu hv hnv h2 hle
      exact ⟨b1, b2, b5, b6, b3, b4, b7, b8⟩

/-- `nat.rem` (natdiv.go:505-513): the remainder of `nat.div` (quotient storage `qs` = `stk.nat(max(1, len u - (len v - 1)))`). -/
def natRem (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs u v : List Nat) : List Nat :=
  (natDiv dr qs u v).2

theorem natRem_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs u v : List Nat) (hu : Wd u) (hv : Wd v) (hnu : Normed u) (hnv : Normed v) (hve : v ≠ [])
    (hqs : Wd qs) (hqsl : qs.length = max 1 (u.length - (v.length - 1))) :
    Wd (natRem dr qs u v) ∧ Normed (natRem dr qs u v) ∧ val (natRem dr qs u v) = val u % val v ∧
    (natRem dr qs u v).length ≤ v.length := by
  have hvlen : 0 < v.length := List.length_pos_iff.2 hve
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := natDiv_spec dr hdr qs u v hu hv hnu hnv hve hqs
    (fun h2 hle => by rw [hqsl]; omega)
  exact ⟨a2, a4, a6, a8⟩

end FvModexp.Mdl
