import FvModexp.Proofs.Common.Slices
import FvModexp.Proofs.Common.VecOps
import FvModexp.Proofs.Common.DivBasicMath
/-!
# `divBasic`: multiply-subtract-add-back part of one iteration (natdiv.go:703-720)

```go
qhatv[n] = mulAddVWW(qhatv[0:n], v, qhat, 0)
qhl := len(qhatv)
if j+qhl > len(u) && qhatv[n] == 0 { qhl-- }
c := subVV(u[j:j+qhl], u[j:j+qhl], qhatv[:qhl])
if c != 0 {
    c := addVV(u[j:j+n], u[j:j+n], v)
    if n < qhl { u[j+n] += c }
    qhat--
}
```
`dbSubAdd v j qhat u` returns the new `u` and the new `qhat`.  `dbSubAdd_spec` proves (given the Knuth estimate bound
`X/D ≤ qhat ≤ X/D+1`) that afterwards `u[j:]` holds `X % D`, `qhat = X / D`, `u[:j]` untouched, and no slice is out of range.
-/
namespace FvModexp.Mdl

/-- natdiv.go:710-720: given the result `s = (z, c)` of the `subVV` (new window contents, borrow), store it and do the add-back
if `c != 0`. `qhl` is the window length used by the `subVV`. -/
def dbFix (v : List Nat) (j qhat qhl : Nat) (u : List Nat) (s : List Nat × Nat) : List Nat × Nat :=
  let n := v.length
  let u1 := upd u j s.1
  if s.2 ≠ 0 then
    let a := addVV (sl u1 j n) v                           -- c := addVV(u[j:j+n], u[j:j+n], v)
    let u2 := upd u1 j a.1
    let u3 := if n < qhl then upd u2 (j + n) [(u2.getD (j + n) 0 + a.2) % 2 ^ 64] else u2   -- u[j+n] += c
    (u3, (qhat + 2 ^ 64 - 1) % 2 ^ 64)                     -- qhat--
  else (u1, qhat)

/-- natdiv.go:703-720. `n = len v`. -/
def dbSubAdd (v : List Nat) (j qhat : Nat) (u : List Nat) : List Nat × Nat :=
  let n := v.length
  let p := mulAddVWW v qhat 0                              -- qhatv[n] = mulAddVWW(qhatv[0:n], v, qhat, 0)
  let qhl := if j + (n + 1) > u.length ∧ p.2 = 0 then n else n + 1
  dbFix v j qhat qhl u (subVV (sl u j qhl) ((p.1 ++ [p.2]).take qhl))   -- c := subVV(u[j:j+qhl], u[j:j+qhl], qhatv[:qhl])

/-! ### list lemmas -/

theorem upd_app (A W l : List Nat) (i : Nat) : upd (A ++ W) (A.length + i) l = A ++ upd W i l := by
  unfold upd
  rw [List.take_append, List.drop_append, List.take_of_length_le (by omega)]
  have e1 : A.length + i - A.length = i := by omega
  rw [e1]
  have e2 : A.length + i + l.length - A.length = i + l.length := by omega
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append, e2]
  simp [List.append_assoc]

theorem sl_app (A W : List Nat) (K : Nat) : sl (A ++ W) A.length K = sl W 0 K := by
  simp [sl, List.drop_append]

theorem length_upd' (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) : (upd z i l).length = z.length :=
  length_upd z l i h

theorem upd_zero (W l : List Nat) : upd W 0 l = l ++ W.drop l.length := by simp [upd]

theorem sl_zero (W : List Nat) (K : Nat) : sl W 0 K = W.take K := by simp [sl]

theorem upd_app0 (A W l : List Nat) : upd (A ++ W) A.length l = A ++ upd W 0 l := by
  simpa using upd_app A W l 0

theorem getD_app (A W : List Nat) (i : Nat) : (A ++ W).getD (A.length + i) 0 = W.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem dbFix_app (v : List Nat) (qhat qhl : Nat) (A W : List Nat) (s : List Nat × Nat) :
    dbFix v A.length qhat qhl (A ++ W) s = (A ++ (dbFix v 0 qhat qhl W s).1, (dbFix v 0 qhat qhl W s).2) := by
  unfold dbFix
  simp only [sl_app, upd_app0, getD_app, upd_app]
  by_cases hs : s.2 ≠ 0
  · have hs' : (s.2 ≠ 0) = True := eq_true hs
    simp only [hs', ↓reduceIte, Nat.zero_add]
    by_cases hq : v.length < qhl <;> simp only [hq, ↓reduceIte]
  · have hs' : (s.2 ≠ 0) = False := eq_false hs
    simp only [hs', ↓reduceIte]

theorem dbSubAdd_app (v : List Nat) (qhat : Nat) (A W : List Nat) :
    dbSubAdd v A.length qhat (A ++ W) = (A ++ (dbSubAdd v 0 qhat W).1, (dbSubAdd v 0 qhat W).2) := by
  unfold dbSubAdd
  have hc : (A.length + (v.length + 1) > (A ++ W).length ∧ (mulAddVWW v qhat 0).2 = 0) ↔
      (0 + (v.length + 1) > W.length ∧ (mulAddVWW v qhat 0).2 = 0) := by
    simp only [List.length_append]; omega
  simp only [hc, sl_app]
  exact dbFix_app _ _ _ _ _ _


theorem take_len_eq {l : List Nat} {k : Nat} (h : l.length = k) : l.take k = l := by
  rw [← h]; exact List.take_length

/-- The store + add-back (natdiv.go:710-720) at window offset 0, in terms of the borrow outcome of the subtraction.
`s = (z, c)`: new window contents `z` (length `K`) and borrow `c`.  `X = val W`, `D = val v`; hypotheses `hL`/`hR` are the two
outcomes of `iter_core` (no borrow / borrow). -/
theorem dbFix_spec (v W : List Nat) (s : List Nat × Nat) (qhat K : Nat)
    (hv : Wd v) (hW : Wd W) (hqB : qhat < 2 ^ 64) (hn : 2 ≤ v.length) (hK : K = v.length ∨ K = v.length + 1) (hKW : K ≤ W.length)
    (hz : val (W.drop K) = 0) (hs1 : s.1.length = K) (hs2 : Wd s.1) (hs3 : s.2 ≤ 1)
    (hD : 0 < val v)
    (hL : s.2 = 0 → val s.1 = val W % val v ∧ qhat = val W / val v)
    (hR : s.2 = 1 → qhat = val W / val v + 1 ∧ 2 ^ (64 * K) ≤ val s.1 + val v ∧
        val s.1 + val v - 2 ^ (64 * K) = val W % val v) :
    (dbFix v 0 qhat K W s).1.length = W.length ∧ Wd (dbFix v 0 qhat K W s).1 ∧
    val (dbFix v 0 qhat K W s).1 = val W % val v ∧ (dbFix v 0 qhat K W s).2 = val W / val v := by
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have hmodlt : val W % val v < val v := Nat.mod_lt _ hD
  have hWK : (W.drop K).length = W.length - K := by simp
  unfold dbFix
  generalize val W / val v = Q at *
  generalize val W % val v = Rm at *
  by_cases hb : s.2 ≠ 0
  · have hb1 : s.2 = 1 := by omega
    have hb' : (s.2 ≠ 0) = True := eq_true hb
    simp only [hb', ↓reduceIte]
    obtain ⟨hq1, hq2, hq3⟩ := hR hb1
    have hu1 : upd W 0 s.1 = s.1 ++ W.drop K := by rw [upd_zero, hs1]
    have hsl : sl (upd W 0 s.1) 0 v.length = s.1.take v.length := by
      rw [hu1, sl_zero, List.take_append_of_le_length (by omega)]
    rw [hsl]
    have hs1n : (s.1.take v.length).length = v.length := by simp; omega
    obtain ⟨a1, a2, a3, a4⟩ := addVVc_spec (s.1.take v.length) v 0 (hs2.take _) hv hs1n (by omega)
    rw [hs1n] at a1 a4
    have hadd : addVV (s.1.take v.length) v = addVVc (s.1.take v.length) v 0 := rfl
    rw [hadd]
    generalize addVVc (s.1.take v.length) v 0 = a at *
    have hu2 : upd (upd W 0 s.1) 0 a.1 = a.1 ++ (s.1.drop v.length ++ W.drop K) := by
      rw [hu1, upd_zero, a1, List.drop_append_of_le_length (by omega)]
    have hval_s : val s.1 = val (s.1.take v.length) + 2 ^ (64 * v.length) * val (s.1.drop v.length) :=
      val_split s.1 v.length (by omega)
    rcases hK with hK | hK
    · subst hK
      have hd : s.1.drop v.length = [] := List.drop_eq_nil_of_le (by omega)
      have hq : ¬ (v.length < v.length) := Nat.lt_irrefl _
      simp only [hq, ↓reduceIte, hu2, hd, List.nil_append]
      have ha : a.2 = 1 := by
        rcases (show a.2 = 0 ∨ a.2 = 1 by omega) with h | h
        · exfalso
          have := val_lt a2
          rw [a1] at this
          simp only [hd, val_nil] at hval_s
          rw [h] at a4; omega
        · exact h
      have hvs : val (s.1.take v.length) = val s.1 := by simp only [hd, val_nil] at hval_s; omega
      refine ⟨?_, Wd_append.2 ⟨a2, hW.drop _⟩, ?_, ?_⟩
      · simp [a1]; omega
      · rw [val_append, hz]; rw [ha] at a4; rw [a1]; omega
      · have : (qhat + 2 ^ 64 - 1) % 2 ^ 64 = qhat - 1 := by
          have hq1' : 1 ≤ qhat := by omega
          have : qhat + 2 ^ 64 - 1 = (qhat - 1) + 2 ^ 64 := by omega
          rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        simp only [this]
        omega
    · subst hK
      have hq : v.length < v.length + 1 := Nat.lt_succ_self _
      have hlenW : s.1.length = v.length + 1 := hs1
      have hdl : (s.1.drop v.length).length = 1 := by simp [hlenW]
      obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 hdl
      have htB : t < 2 ^ 64 := hs2 t (List.mem_of_mem_drop (by rw [ht]; simp))
      have hg : (a.1 ++ (t :: W.drop (v.length + 1))).getD v.length 0 = t := by
        rw [← a1]; simpa using getD_app a.1 (t :: W.drop (v.length + 1)) 0
      have hu3 : upd (a.1 ++ (t :: W.drop (v.length + 1))) v.length [(t + a.2) % 2 ^ 64] =
          a.1 ++ ((t + a.2) % 2 ^ 64 :: W.drop (v.length + 1)) := by
        have := upd_app a.1 (t :: W.drop (v.length + 1)) [(t + a.2) % 2 ^ 64] 0
        rw [a1] at this
        simpa [upd_zero] using this
      simp only [hq, ↓reduceIte, Nat.zero_add, hu2, ht, List.singleton_append, hg, hu3]
      have htk : val (s.1.drop v.length) = t := by rw [ht]; simp
      rw [htk] at hval_s
      have hP : 2 ^ (64 * (v.length + 1)) = 2 ^ 64 * 2 ^ (64 * v.length) := pow_succ64 _
      rw [hP] at hq2 hq3
      have hvlt := val_lt a2
      rw [a1] at hvlt
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [a1]; omega
      · exact Wd_append.2 ⟨a2, Wd_cons.2 ⟨Nat.mod_lt _ (by omega), hW.drop _⟩⟩
      · rw [val_append, val_cons, hz, a1]
        generalize 2 ^ (64 * v.length) = P at *
        generalize 2 ^ 64 = E at *
        have hc := Nat.mul_comm P E
        have hat : a.2 + t = E := by
          refine Nat.le_antisymm (by omega) (Nat.le_of_not_lt (fun hlt => ?_))
          have h1 : P * (a.2 + t) ≤ P * (E - 1) := Nat.mul_le_mul_left _ (by omega)
          have h2 : P * (E - 1) + P = P * E := by
            have : E - 1 + 1 = E := by omega
            calc P * (E - 1) + P = P * (E - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
              _ = P * E := by rw [this]
          have h3 : P * (a.2 + t) = P * a.2 + P * t := Nat.mul_add _ _ _
          omega
        have hx : (t + a.2) % E = 0 := by
          rw [Nat.add_comm, hat]; exact Nat.mod_self _
        rw [hx]
        have h3 : P * (a.2 + t) = P * a.2 + P * t := Nat.mul_add _ _ _
        rw [hat] at h3
        omega
      · have hq1' : 1 ≤ qhat := by omega
        have : (qhat + 2 ^ 64 - 1) % 2 ^ 64 = qhat - 1 := by
          have : qhat + 2 ^ 64 - 1 = (qhat - 1) + 2 ^ 64 := by omega
          rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        simp only [this]
        omega
  · have hb' : (s.2 ≠ 0) = False := eq_false hb
    simp only [hb', ↓reduceIte]
    have hb0 : s.2 = 0 := by omega
    obtain ⟨h1, h2⟩ := hL hb0
    have hu1 : upd W 0 s.1 = s.1 ++ W.drop K := by rw [upd_zero, hs1]
    simp only [hu1]
    refine ⟨?_, Wd_append.2 ⟨hs2, hW.drop _⟩, ?_, h2⟩
    · simp [hs1]; omega
    · rw [val_append, hz, hs1]; omega


/-- Subtract `y = qhat * v` (as a `K`-limb window) from the window `W[0:K]`, then fix up (natdiv.go:708-720). -/
theorem dbCore (v W y : List Nat) (qhat K : Nat)
    (hv : Wd v) (hW : Wd W) (hqB : qhat < 2 ^ 64) (hn : 2 ≤ v.length) (hK : K = v.length ∨ K = v.length + 1)
    (hKW : K ≤ W.length) (hz : val (W.drop K) = 0) (hyl : y.length = K) (hyW : Wd y) (hyv : val y = qhat * val v)
    (hD : 0 < val v) (hqh : val W / val v ≤ qhat ∧ qhat ≤ val W / val v + 1) (hXK : val W < 2 ^ (64 * K)) :
    (dbFix v 0 qhat K W (subVV (sl W 0 K) y)).1.length = W.length ∧ Wd (dbFix v 0 qhat K W (subVV (sl W 0 K) y)).1 ∧
    val (dbFix v 0 qhat K W (subVV (sl W 0 K) y)).1 = val W % val v ∧
    (dbFix v 0 qhat K W (subVV (sl W 0 K) y)).2 = val W / val v := by
  have hsl : sl W 0 K = W.take K := sl_zero W K
  have hxl : (W.take K).length = K := by simp; omega
  have hxv : val (W.take K) = val W := by
    have := val_split W K hKW
    rw [hz] at this; omega
  obtain ⟨s1, s2, s3, s4⟩ := subVVc_spec (W.take K) y 0 (hW.take _) hyW (by omega) (by omega)
  rw [hxl] at s1 s4
  have hsub : subVV (sl W 0 K) y = subVVc (W.take K) y 0 := by rw [hsl]; rfl
  rw [hsub]
  generalize subVVc (W.take K) y 0 = s at *
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have hPK : 2 ^ (64 * v.length) ≤ 2 ^ (64 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  have hrlt := val_lt s2
  rw [s1] at hrlt
  have hic := Knuth.iter_core (2 ^ (64 * K)) (val v) (val W) (val W) 0 qhat s.2 (val s.1) (by omega) hD hXK
    (by omega) hqh (by have c1 := Nat.mul_comm s.2 (2 ^ (64 * K)); have c2 := Nat.mul_comm qhat (val v); rw [hyv, hxv] at s4; omega) hrlt
  refine dbFix_spec v W s qhat K hv hW hqB hn hK hKW hz s1 s2 s3 hD ?_ ?_
  · intro h0
    rcases hic with ⟨_, h2, h3⟩ | ⟨h1, _⟩
    · exact ⟨h3, h2⟩
    · omega
  · intro h1
    rcases hic with ⟨h1', _⟩ | ⟨_, h2, h3, h4⟩
    · omega
    · exact ⟨h2, h3, h4⟩


/-- One multiply-subtract-add-back round on the window `W = u[j:]` (offset 0 form).  Hypotheses: `W` holds `n..` limbs, everything
above the `(n+1)`-limb window is zero, `X = val W < B * D` and the estimate satisfies `X/D ≤ qhat ≤ X/D + 1`; `hcar` says
`qhat * v` fits in `n` limbs when the window has only `n` limbs (so `qhatv[n] == 0` and the `qhl--` branch is taken).
Conclusion: `W` becomes `X % D`, `qhat` becomes `X / D`, same length; `W.length = n → qhatv[n] = 0`, i.e. `u[j:j+qhl]` is in range. -/
theorem dbSubAddW_spec (v W : List Nat) (qhat : Nat)
    (hv : Wd v) (hW : Wd W) (hqB : qhat < 2 ^ 64) (hn : 2 ≤ v.length) (hnW : v.length ≤ W.length)
    (hD : 0 < val v) (hz : val (W.drop (v.length + 1)) = 0)
    (hqh : val W / val v ≤ qhat ∧ qhat ≤ val W / val v + 1) (hXD : val W < 2 ^ 64 * val v)
    (hcar : W.length = v.length → qhat * val v < 2 ^ (64 * v.length)) :
    (dbSubAdd v 0 qhat W).1.length = W.length ∧ Wd (dbSubAdd v 0 qhat W).1 ∧
    val (dbSubAdd v 0 qhat W).1 = val W % val v ∧ (dbSubAdd v 0 qhat W).2 = val W / val v ∧
    (W.length = v.length → (mulAddVWW v qhat 0).2 = 0) := by
  obtain ⟨p1, p2, p3, p4⟩ := mulAddVWW_spec v qhat 0 hv hqB (by omega)
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have hcarry : W.length = v.length → (mulAddVWW v qhat 0).2 = 0 := by
    intro h
    have := hcar h
    refine Nat.eq_zero_of_not_pos (fun hne => ?_)
    have : 2 ^ (64 * v.length) ≤ 2 ^ (64 * v.length) * (mulAddVWW v qhat 0).2 :=
      Nat.le_mul_of_pos_right _ hne
    have c := Nat.mul_comm (val v) qhat
    omega
  unfold dbSubAdd
  dsimp only
  by_cases hc1 : 0 + (v.length + 1) > W.length ∧ (mulAddVWW v qhat 0).2 = 0
  · rw [if_pos hc1]
    have hWn : W.length = v.length := by omega
    have hy : (((mulAddVWW v qhat 0).1 ++ [(mulAddVWW v qhat 0).2]).take v.length) = (mulAddVWW v qhat 0).1 := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hy]
    have h2 := hc1.2
    rw [h2] at p4
    have hXK := val_lt hW
    rw [hWn] at hXK
    obtain ⟨c1, c2, c3, c4⟩ := dbCore v W (mulAddVWW v qhat 0).1 qhat v.length hv hW hqB hn (Or.inl rfl) hnW
      (by rw [List.drop_eq_nil_of_le (by omega)]; rfl) p1 p2 (by have := Nat.mul_comm (val v) qhat; omega) hD hqh hXK
    exact ⟨c1, c2, c3, c4, hcarry⟩
  · rw [if_neg hc1]
    have hWn : v.length + 1 ≤ W.length := by
      refine Nat.le_of_not_lt (fun h => hc1 ⟨by omega, hcarry (by omega)⟩)
    have hy : (((mulAddVWW v qhat 0).1 ++ [(mulAddVWW v qhat 0).2]).take (v.length + 1)) =
        (mulAddVWW v qhat 0).1 ++ [(mulAddVWW v qhat 0).2] := by
      apply take_len_eq; simp [p1]
    rw [hy]
    have hXK : val W < 2 ^ (64 * (v.length + 1)) := by
      rw [pow_succ64]
      have : 2 ^ 64 * val v ≤ 2 ^ 64 * 2 ^ (64 * v.length) := Nat.mul_le_mul_left _ (Nat.le_of_lt hDlt)
      omega
    obtain ⟨c1, c2, c3, c4⟩ := dbCore v W ((mulAddVWW v qhat 0).1 ++ [(mulAddVWW v qhat 0).2]) qhat (v.length + 1) hv hW hqB hn
      (Or.inr rfl) hWn hz (by simp [p1]) (Wd_append.2 ⟨p2, by intro d hd; simp at hd; subst hd; exact p3⟩)
      (by have e : val ((mulAddVWW v qhat 0).1 ++ [(mulAddVWW v qhat 0).2]) = val (mulAddVWW v qhat 0).1 + 2 ^ (64 * v.length) * (mulAddVWW v qhat 0).2 := by rw [val_append, p1]; simp
          have := Nat.mul_comm (val v) qhat; omega) hD hqh hXK
    exact ⟨c1, c2, c3, c4, hcarry⟩


/-- `dbSubAddW_spec` at window offset `j` of the full `u`. -/
theorem dbSubAdd_spec (v u : List Nat) (j qhat : Nat)
    (hv : Wd v) (hu : Wd u) (hqB : qhat < 2 ^ 64) (hn : 2 ≤ v.length) (hj : j + v.length ≤ u.length)
    (hD : 0 < val v) (hz : val (u.drop (j + v.length + 1)) = 0)
    (hqh : val (u.drop j) / val v ≤ qhat ∧ qhat ≤ val (u.drop j) / val v + 1) (hXD : val (u.drop j) < 2 ^ 64 * val v)
    (hcar : u.length = j + v.length → qhat * val v < 2 ^ (64 * v.length)) :
    (dbSubAdd v j qhat u).1.length = u.length ∧ Wd (dbSubAdd v j qhat u).1 ∧
    (dbSubAdd v j qhat u).1.take j = u.take j ∧
    val ((dbSubAdd v j qhat u).1.drop j) = val (u.drop j) % val v ∧
    (dbSubAdd v j qhat u).2 = val (u.drop j) / val v ∧
    (u.length = j + v.length → (mulAddVWW v qhat 0).2 = 0) := by
  obtain ⟨A, W, rfl, hA⟩ : ∃ A W, u = A ++ W ∧ A.length = j :=
    ⟨u.take j, u.drop j, (List.take_append_drop _ _).symm, by simp; omega⟩
  subst hA
  rw [dbSubAdd_app]
  simp only [List.length_append, List.take_left, List.drop_left] at *
  have hW := hu
  rw [Wd_append] at hW
  have hzW : val (W.drop (v.length + 1)) = 0 := by
    have : (A ++ W).drop (A.length + v.length + 1) = W.drop (v.length + 1) := by
      rw [Nat.add_assoc, ← List.drop_drop, List.drop_left]
    simpa [this] using hz
  obtain ⟨c1, c2, c3, c4, c5⟩ := dbSubAddW_spec v W qhat hv hW.2 hqB hn (by omega) hD hzW hqh hXD
    (fun h => hcar (by omega))
  refine ⟨by omega, Wd_append.2 ⟨hW.1, c2⟩, by simp, ?_, c4, fun h => c5 (by omega)⟩
  simpa using c3

end FvModexp.Mdl
