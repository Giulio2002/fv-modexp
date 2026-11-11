import FvModexp.Proofs.Common.DivBasicList
import FvModexp.Proofs.Common.DivBasicStep

/-!
# `divBasic`: from the machine's word-level facts of one loop iteration to the model `Mdl.dbSubAdd` (ISA independent)

`su_bridge`: the multiply (`qhatv = v·qhat`), the subtract on the window `u[j:j+qhl]`, the add-back, stated as
`readLE`/`lv` facts about the memories after each call, give `limbs` of `u` = `(Mdl.dbSubAdd …).1` and the final
`qhat` = `(Mdl.dbSubAdd …).2`.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

theorem limbs_succ_last (m : Memory) : ∀ (p n : Nat), limbs m p (n + 1) = limbs m p n ++ [m.readLE (p + 8 * n) 8]
  | p, 0 => by simp [limbs]
  | p, n + 1 => by
    show m.readLE p 8 :: limbs m (p + 8) (n + 1) = (m.readLE p 8 :: limbs m (p + 8) n) ++ _
    rw [limbs_succ_last m (p + 8) n, show p + 8 * (n + 1) = p + 8 + 8 * n by omega]
    simp only [List.cons_append]

theorem limbs_take (m : Memory) : ∀ (p n k : Nat), k ≤ n → (limbs m p n).take k = limbs m p k
  | _, _, 0, _ => by simp [limbs]
  | _, 0, _ + 1, h => by omega
  | p, n + 1, k + 1, h => by
    simp only [limbs, List.take_succ_cons]
    rw [limbs_take m (p + 8) n k (by omega)]

theorem upd_append2 (z a b : List Nat) (i : Nat) (h : i + a.length + b.length ≤ z.length) :
    Mdl.upd z i (a ++ b) = Mdl.upd (Mdl.upd z i a) (i + a.length) b := by
  unfold Mdl.upd
  have h1 : (z.take i).length = i := by simp; omega
  have e1 : (z.take i ++ a ++ z.drop (i + a.length)).take (i + a.length) = z.take i ++ a := by
    rw [List.take_append, List.take_append]
    simp only [List.length_append, h1]
    rw [List.take_of_length_le (by rw [h1]; omega), show i + a.length - i = a.length by omega,
      List.take_of_length_le (Nat.le_refl _), Nat.sub_self, List.take_zero, List.append_nil]
  have e2 : (z.take i ++ a ++ z.drop (i + a.length)).drop (i + a.length + b.length) =
      z.drop (i + (a ++ b).length) := by
    rw [List.drop_append]
    simp only [List.length_append, h1, List.drop_drop]
    have : (List.drop (i + a.length + b.length) (List.take i z ++ a)) = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [this, List.nil_append]
    congr 1; omega
  rw [e1, e2]; simp

theorem getD_upd_far (z l : List Nat) (i k : Nat) (h : i + l.length ≤ k) :
    (Mdl.upd z i l).getD k 0 = z.getD k 0 := by
  unfold Mdl.upd
  by_cases hk : i + l.length ≤ z.length
  · have h1 : (z.take i ++ l).length = i + l.length := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h1,
      List.getElem?_drop]
    congr 2; omega
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (l := z) (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]

theorem lv_eq_val (m : Memory) (p n : Nat) : lv m p n = Mdl.val (limbs m p n) := (val_limbs m p n).symm

/-- One iteration's multiply / subtract / add-back, from the word-level facts of the machine. -/
theorem su_bridge (M0 M2 M3 M4 Mv : Memory) (up ul vp vl t j qhat c bw q : Nat) (hq : qhat < 2 ^ 64)
    (hm1 : lv M2 t vl = lv Mv vp vl * qhat % 2 ^ (64 * vl)) (hm2 : c = lv Mv vp vl * qhat / 2 ^ (64 * vl))
    (hU2 : ∀ i < ul, M2.readLE (up + 8 * i) 8 = M0.readLE (up + 8 * i) 8)
    (hqd : q = if ul < j + (vl + 1) ∧ c = 0 then vl else vl + 1) (hj : j + q ≤ ul)
    (hT : ∀ i < vl, M3.readLE (t + 8 * i) 8 = M2.readLE (t + 8 * i) 8) (hTc : M3.readLE (t + 8 * vl) 8 = c)
    (hU3 : ∀ i < ul, (i < j ∨ j + q ≤ i) → M3.readLE (up + 8 * i) 8 = M2.readLE (up + 8 * i) 8)
    (hsv : lv M3 (up + 8 * j) q + lv M3 t q = lv M2 (up + 8 * j) q + 2 ^ (64 * q) * bw) (hbw : bw ≤ 1)
    (hU4 : ∀ i < ul, (i < j ∨ j + q ≤ i) → M4.readLE (up + 8 * i) 8 = M3.readLE (up + 8 * i) 8)
    (hz : bw = 0 → ∀ i < ul, M4.readLE (up + 8 * i) 8 = M3.readLE (up + 8 * i) 8)
    (hnz : bw ≠ 0 → ∃ ca, lv M4 (up + 8 * j) vl + 2 ^ (64 * vl) * ca = lv M3 (up + 8 * j) vl + lv Mv vp vl ∧
      (vl < q → M4.readLE (up + 8 * j + 8 * vl) 8 = (M3.readLE (up + 8 * j + 8 * vl) 8 + ca) % 2 ^ 64)) :
    limbs M4 up ul = (Mdl.dbSubAdd (limbs Mv vp vl) j qhat (limbs M0 up ul)).1 ∧
      (if bw = 0 then qhat else (qhat + 2 ^ 64 - 1) % 2 ^ 64) =
        (Mdl.dbSubAdd (limbs Mv vp vl) j qhat (limbs M0 up ul)).2 := by
  -- the product
  obtain ⟨hpl, hpw, hp2, hpv⟩ := Mdl.mulAddVWW_spec (limbs Mv vp vl) qhat 0 (Wd_limbs _ _ _) hq (by omega)
  simp only [length_limbs, val_limbs, Nat.add_zero] at hpl hpv
  generalize hp : Mdl.mulAddVWW (limbs Mv vp vl) qhat 0 = p at hpl hpw hp2 hpv
  obtain ⟨e1, e2⟩ := limbs_of_value M2 t vl c p.1 p.2 hpw hpl (by
    rw [hpv, hm1, hm2]; exact Nat.mod_add_div _ _)
  subst e2
  -- `qhatv[:qhl]` in `M3`
  have hY : limbs M3 t (vl + 1) = p.1 ++ [p.2] := by
    rw [limbs_succ_last, hTc, ← e1]
    congr 1; exact limbs_ext hT
  have hq1 : q ≤ vl + 1 := by rw [hqd]; split <;> omega
  have hY' : limbs M3 t q = (p.1 ++ [p.2]).take q := by rw [← hY, limbs_take _ _ _ _ hq1]
  -- the window of `u` before the subtraction
  have hX : Mdl.sl (limbs M0 up ul) j q = limbs M2 (up + 8 * j) q := by
    rw [sl_limbs _ _ _ _ _ hj]; symm; apply limbs_ext; intro i hi
    rw [show up + 8 * j + 8 * i = up + 8 * (j + i) by omega]; exact hU2 _ (by omega)
  -- the subtraction
  obtain ⟨hs1, hs2⟩ := subVV_list (limbs M2 (up + 8 * j) q) (limbs M3 t q) (limbs M3 (up + 8 * j) q) bw
    (Wd_limbs _ _ _) (Wd_limbs _ _ _) (Wd_limbs _ _ _) (by simp) (by simp) hbw (by
      simp only [val_limbs, length_limbs]; exact hsv)
  have hU30 : limbs M3 up ul = Mdl.upd (limbs M0 up ul) j (limbs M3 (up + 8 * j) q) :=
    limbs_upd hj fun i hi h => (hU3 i hi h).trans (hU2 i hi)
  have hqe : (if ul < j + (vl + 1) ∧ p.2 = 0 then vl else vl + 1) = q := hqd.symm
  simp only [Mdl.dbSubAdd, length_limbs, hp, gt_iff_lt, hqe, hX, ← hY']
  generalize hs : Mdl.subVV (limbs M2 (up + 8 * j) q) (limbs M3 t q) = sr at hs1 hs2
  rw [show sr = (limbs M3 (up + 8 * j) q, bw) from Prod.ext hs1.symm hs2.symm]
  simp only [Mdl.dbFix, length_limbs, ← hU30]
  by_cases hb0 : bw = 0
  · subst hb0
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, and_true]
    exact limbs_ext (hz rfl)
  · obtain ⟨ca, hca1, hca2⟩ := hnz hb0
    simp only [ne_eq, hb0, not_false_eq_true, ↓reduceIte, and_true]
    -- the add-back on `u[j:j+n]`
    have hX' : Mdl.sl (limbs M3 up ul) j vl = limbs M3 (up + 8 * j) vl := sl_limbs _ _ _ _ _ (by
      rw [hqd] at hj; split at hj <;> omega)
    obtain ⟨ha1, ha2⟩ := addVV_list (limbs M3 (up + 8 * j) vl) (limbs Mv vp vl) (limbs M4 (up + 8 * j) vl) ca
      (Wd_limbs _ _ _) (Wd_limbs _ _ _) (Wd_limbs _ _ _) (by simp) (by simp) (by
        simp only [val_limbs, length_limbs]; exact hca1)
    rw [hX']
    generalize ha : Mdl.addVV (limbs M3 (up + 8 * j) vl) (limbs Mv vp vl) = ar at ha1 ha2
    rw [show ar = (limbs M4 (up + 8 * j) vl, ca) from Prod.ext ha1.symm ha2.symm]
    have hU43 : limbs M4 up ul = Mdl.upd (limbs M3 up ul) j (limbs M4 (up + 8 * j) q) := limbs_upd hj hU4
    by_cases hvq : vl < q
    · have hq' : q = vl + 1 := by omega
      rw [if_pos hvq, hU43, hq', limbs_succ_last, upd_append2 _ _ _ _ (by simp; omega)]
      simp only [length_limbs]
      rw [getD_upd_far _ _ _ _ (by simp), limbs_getD _ _ _ _ (by omega),
        show up + 8 * (j + vl) = up + 8 * j + 8 * vl by omega, ← hca2 hvq]
    · have h2 : q = vl ∨ q = vl + 1 := by rw [hqd]; split <;> simp
      have hq' : q = vl := by omega
      rw [if_neg hvq, hU43, hq']

end FvModexp.Asm
