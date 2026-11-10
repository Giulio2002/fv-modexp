import FvModexp.Proofs.Common.DivRecFin
/-!
# `divRecursive` / `divRecursiveStep` (natdiv.go:740-892): the recursion and the contract

`drs db mul f z u0 v0` models `z.divRecursiveStep(stk, u0, v0, depth)` with recursion fuel `f` (the recursion is on `len(v)`, which
drops from `n` to `n - n/2 + 1 < n`, so fuel `len v + 1` suffices).  `db` is the `divBasic` callee (`DivBasicContract db`), `mul` the
multiplier callee (`MulContract mul`).  `drs` returns the final contents of `z` and of `u0` (updated in place; `u = u.norm()` is a
prefix of `u0`, the rest is untouched).
-/
namespace FvModexp.Mdl

/-- natdiv.go:750-892. -/
def drs (db : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat) :
    Nat → List Nat → List Nat → List Nat → List Nat × List Nat
  | 0, z, u, _ => (z, u)
  | f + 1, z, u0, v0 =>
    if (norm u0).length = 0 then (List.replicate z.length 0, u0)
    else if (norm v0).length < 40 then
      ((db z (norm u0) (norm v0)).1, (db z (norm u0) (norm v0)).2 ++ u0.drop (norm u0).length)
    else if (norm u0).length < (norm v0).length then (z, u0)
    else
      let n := (norm v0).length
      let m := (norm u0).length - n
      let B := n / 2
      let L := drsLoop (fun a b c => drs db mul f a b c) mul (norm v0) n B m m z (norm u0)
      let F := finalBlock (fun a b c => drs db mul f a b c) mul (norm v0) n B L.1 L.2
      (F.1, F.2 ++ u0.drop (norm u0).length)

/-- natdiv.go:740-743: `clear(z); z.divRecursiveStep(stk, u, v, 0)`. -/
def divRecursive (db : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (z u v : List Nat) : List Nat × List Nat :=
  drs db mul (v.length + 1) (List.replicate z.length 0) u v

/-- Conclusion of a division step. -/
def Conc (z u v z' u' : List Nat) : Prop :=
  z'.length = z.length ∧ u'.length = u.length ∧ Wd z' ∧ Wd u' ∧ val z' = val u / val v ∧ val u' = val u % val v ∧
  ∀ d ∈ u'.drop v.length, d = 0

theorem normed_of_top : ∀ (l : List Nat), 2 ^ 63 ≤ topLimb l → Normed l
  | [], h => by simp [topLimb] at h
  | [d], h => by
    simp only [topLimb] at h
    rw [normed_cons]
    exact ⟨rfl, fun ⟨_, h2⟩ => by simp at h; omega⟩
  | d :: e :: es, h => by
    have : topLimb (d :: e :: es) = topLimb (e :: es) := by simp [topLimb]
    rw [this] at h
    rw [normed_cons]
    exact ⟨normed_of_top (e :: es) h, fun ⟨h1, _⟩ => by simp at h1⟩

theorem conc_small (z u v : List Nat) (hz0 : ∀ d ∈ z, d = 0) (hu : Wd u) (hv : Wd v) (hlt : val u < val v) :
    Conc z u v z u := by
  have hzv : val z = 0 := val_eq_zero_iff.2 hz0
  have hvlt : val v < 2 ^ (64 * v.length) := val_lt hv
  refine ⟨rfl, rfl, fun d hd => by have := hz0 d hd; omega, hu, ?_, ?_, ?_⟩
  · rw [hzv, Nat.div_eq_of_lt hlt]
  · rw [Nat.mod_eq_of_lt hlt]
  · exact zero_drop_of_lt hu (Nat.lt_trans hlt hvlt)

theorem wrap_spec (u0 w : List Nat) (hu : Wd u0) (hw : Wd w) (hwl : w.length = (norm u0).length) :
    (w ++ u0.drop (norm u0).length).length = u0.length ∧ Wd (w ++ u0.drop (norm u0).length) ∧
    val (w ++ u0.drop (norm u0).length) = val w := by
  obtain ⟨k, hk, hnk, hzk⟩ := norm_eq_take u0
  have hl : (norm u0).length = k := by rw [hnk]; simp; omega
  rw [hl] at hwl ⊢
  have hz : val (u0.drop k) = 0 := val_eq_zero_iff.2 hzk
  refine ⟨by simp [hwl]; omega, Wd_append.2 ⟨hw, hu.drop _⟩, ?_⟩
  rw [val_append, hz]; simp


theorem conc_small2 (z z' u0 u1 v : List Nat) (hz0 : ∀ d ∈ z', d = 0) (hzl : z'.length = z.length) (hu1 : Wd u1)
    (hl : u1.length = u0.length) (hval : val u1 = val u0) (hlt : val u0 < val v) (hv : Wd v) : Conc z u0 v z' u1 := by
  have hzv : val z' = 0 := val_eq_zero_iff.2 hz0
  have hvlt : val v < 2 ^ (64 * v.length) := val_lt hv
  refine ⟨hzl, hl, fun d hd => by have := hz0 d hd; omega, hu1, ?_, ?_, ?_⟩
  · rw [hzv, Nat.div_eq_of_lt hlt]
  · rw [hval, Nat.mod_eq_of_lt hlt]
  · exact zero_drop_of_lt hu1 (by rw [hval]; exact Nat.lt_trans hlt hvlt)

theorem short_lt (u v : List Nat) (hu : Wd u) (hv : Wd v) (h2 : v ≠ []) (htop : 2 ^ 63 ≤ topLimb v)
    (hlt : u.length < v.length) : val u < val v := by
  have h1 := val_lt hu
  have hvge := val_ge_top h2 htop
  have : 2 ^ (64 * u.length) ≤ 2 ^ (64 * (v.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have : 2 ^ (64 * (v.length - 1)) ≤ 2 ^ 63 * 2 ^ (64 * (v.length - 1)) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  omega

/-- bounds from `2·u < β^(n+k)` and `v` with top bit set. -/
theorem fit_of_H (v u : List Nat) (hv : Wd v) (htop : 2 ^ 63 ≤ topLimb v) (hn : v.length = n) (k : Nat)
    (hH : 2 * val u < 2 ^ (64 * (n + k))) : val u < val v * 2 ^ (64 * k) := by
  have hne : v ≠ [] := by intro e; subst e; simp [topLimb] at htop
  have h := val_ge_top hne htop
  rw [hn] at h
  have e : 2 ^ (64 * (n + k)) = 2 * (2 ^ 63 * 2 ^ (64 * (n - 1))) * 2 ^ (64 * k) := by
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso; apply hne; exact List.length_eq_zero_iff.1 (by omega)
      · exact h0
    rw [pow64_add, show 64 * n = 64 * (n - 1) + 64 by omega, Nat.pow_add, two_pow_64_eq]
    ac_rfl
  rw [e] at hH
  have : 2 * (2 ^ 63 * 2 ^ (64 * (n - 1))) * 2 ^ (64 * k) ≤ 2 * val v * 2 ^ (64 * k) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
  rw [Nat.mul_assoc 2 (val v)] at this
  omega

theorem drs_basic (db : List Nat → List Nat → List Nat → List Nat × List Nat) (hdb : DivBasicContract db)
    (z u0 v : List Nat) (hz0 : ∀ d ∈ z, d = 0) (hz : Wd z) (hu : Wd u0) (hv : Wd v) (h2 : 2 ≤ v.length)
    (htop : 2 ^ 63 ≤ topLimb v) (hnorm : norm v = v) (hH : 2 * val u0 < 2 ^ (64 * (v.length + z.length)))
    (hne : (norm u0).length ≠ 0) :
    Conc z u0 v (db z (norm u0) v).1 ((db z (norm u0) v).2 ++ u0.drop (norm u0).length) := by
  have hnu : Wd (norm u0) := Wd_norm hu
  have hvu := val_norm u0
  have hfit := fit_of_H v u0 hv htop rfl z.length hH
  have hvp : 0 < val v := by
    have hne' : v ≠ [] := by intro e; subst e; simp at h2
    have := val_ge_top hne' htop
    have : 0 < 2 ^ 63 * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hvge := val_ge_top (by intro e; subst e; simp at h2) htop
  obtain ⟨hd1, hd2⟩ := hdb z (norm u0) v hz hnu hv h2 htop
  by_cases hlt : (norm u0).length < v.length
  · have hdb1 := hd1 hlt
    rw [hdb1]
    simp only []
    obtain ⟨w1, w2, w3⟩ := wrap_spec u0 (norm u0) hu hnu rfl
    have hvlt : val (norm u0) < val v := by
      have h1 := val_lt hnu
      have : 2 ^ (64 * (norm u0).length) ≤ 2 ^ (64 * (v.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      have : 2 ^ (64 * (v.length - 1)) ≤ 2 ^ 63 * 2 ^ (64 * (v.length - 1)) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      omega
    have := conc_small2 z z u0 _ v hz0 rfl w2 (by rw [w1]) (by rw [w3, hvu]) (by rw [← hvu]; exact hvlt) hv
    exact this
  · have hle : v.length ≤ (norm u0).length := by omega
    -- the quotient fits
    have hlen : (norm u0).length ≤ v.length + z.length := by
      refine length_le_of_normed hnu (normed_norm _) ?_
      rw [hvu]
      have : 2 ^ (64 * (v.length + z.length)) ≤ 2 * 2 ^ (64 * (v.length + z.length)) := by omega
      omega
    have hcond : (norm u0).length - v.length < z.length ∨
        ((norm u0).length - v.length = z.length ∧ val (norm u0) < val v * 2 ^ (64 * z.length)) := by
      by_cases he : (norm u0).length - v.length = z.length
      · exact Or.inr ⟨he, by rw [hvu]; exact hfit⟩
      · exact Or.inl (by omega)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hd2 hle hcond
    obtain ⟨w1, w2, w3⟩ := wrap_spec u0 (db z (norm u0) v).2 hu b4 (by rw [b2])
    have hzdrop : ∀ d ∈ (db z (norm u0) v).1.drop ((norm u0).length - v.length + 1), d = 0 := by
      rw [b6]; intro d hd; exact hz0 d (List.mem_of_mem_drop hd)
    have hvz : val (db z (norm u0) v).1 = val u0 / val v := by
      have := val_take_drop (db z (norm u0) v).1 ((norm u0).length - v.length + 1)
      have hz2 : val ((db z (norm u0) v).1.drop ((norm u0).length - v.length + 1)) = 0 := val_eq_zero_iff.2 hzdrop
      rw [hz2, b5, hvu] at this
      simpa using this
    refine ⟨b1, ?_, b3, w2, hvz, ?_, ?_⟩
    · rw [w1]
    · rw [w3, b7, hvu]
    · refine zero_drop_of_lt w2 ?_
      rw [w3, b7]
      exact Nat.lt_trans (Nat.mod_lt _ hvp) (by have := val_lt hv; exact this)


theorem drs_big (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) (hrec : RecOk rec N)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul)
    (z u0 v : List Nat) (hz0 : ∀ d ∈ z, d = 0) (hz : Wd z) (hu : Wd u0) (hv : Wd v) (h40 : 40 ≤ v.length)
    (htop : 2 ^ 63 ≤ topLimb v) (hH : 2 * val u0 < 2 ^ (64 * (v.length + z.length)))
    (hle : v.length ≤ (norm u0).length) (hnN : v.length - (v.length / 2 - 1) ≤ N) :
    Conc z u0 v
      (finalBlock rec mul v v.length (v.length / 2)
        (drsLoop rec mul v v.length (v.length / 2) ((norm u0).length - v.length) ((norm u0).length - v.length) z (norm u0)).1
        (drsLoop rec mul v v.length (v.length / 2) ((norm u0).length - v.length) ((norm u0).length - v.length) z (norm u0)).2).1
      ((finalBlock rec mul v v.length (v.length / 2)
        (drsLoop rec mul v v.length (v.length / 2) ((norm u0).length - v.length) ((norm u0).length - v.length) z (norm u0)).1
        (drsLoop rec mul v v.length (v.length / 2) ((norm u0).length - v.length) ((norm u0).length - v.length) z (norm u0)).2).2
        ++ u0.drop (norm u0).length) := by
  generalize hnd : v.length = n at *
  have hnu : Wd (norm u0) := Wd_norm hu
  have hvu := val_norm u0
  have hfit := fit_of_H v u0 hv htop hnd z.length hH
  have hvge := val_ge_top (by intro e; subst e; simp at hnd; omega : v ≠ []) htop
  rw [hnd] at hvge
  have hvlt : val v < 2 ^ (64 * n) := by have := val_lt hv; rwa [hnd] at this
  have hvp : 0 < val v := by
    have : 0 < 2 ^ 63 * 2 ^ (64 * (n - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hB1 : 1 ≤ n / 2 := by omega
  have h2B : 2 * (n / 2) ≤ n := by omega
  generalize hm : (norm u0).length - n = m
  generalize hB : n / 2 = B at *
  have hzv : val z = 0 := val_eq_zero_iff.2 hz0
  have hlen : (norm u0).length ≤ n + z.length := by
    refine length_le_of_normed hnu (normed_norm _) ?_
    rw [hvu]
    have : 2 ^ (64 * (n + z.length)) ≤ 2 * 2 ^ (64 * (n + z.length)) := by omega
    omega
  have hmlz : m ≤ z.length := by omega
  have hLI : LI v n B m z.length (val u0) m z (norm u0) := by
    refine ⟨hz, hnu, rfl, by omega, by rw [hzv, hvu]; simp, ?_, ?_, Or.inl rfl⟩
    · have h1 := val_lt hnu
      have e : 2 ^ (64 * (m + 1)) * 2 ^ (64 * (n - 1)) = 2 ^ (64 * ((norm u0).length)) := by
        rw [← pow64_add]; congr 2; omega
      have h3 : 2 ^ 63 * 2 ^ (64 * (n - 1)) * 2 ^ (64 * (m + 1)) ≤ val v * 2 ^ (64 * (m + 1)) := Nat.mul_le_mul_right _ hvge
      have h4 : 2 ^ (64 * (norm u0).length) ≤ 2 ^ 63 * 2 ^ (64 * (n - 1)) * 2 ^ (64 * (m + 1)) := by
        rw [← e]
        exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 63)))
          (Nat.le_of_eq (Nat.mul_comm _ _))
      omega
    · intro d hd
      rw [List.drop_of_length_le (by omega)] at hd
      simp at hd
  obtain ⟨⟨j', hj', hL⟩, _⟩ := drsLoop_spec rec N hrec mul hmul v n B m z.length (val u0) hv hnd htop hB1 h2B hnN hmlz hfit hH
    m m z (norm u0) hLI (Nat.le_refl _)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, _⟩ := finalBlock_spec rec N hrec mul hmul v n B m z.length (val u0) j' _ _ hv hnd htop hB1 h2B hnN hL hj' hfit
  have hvpos := hvp
  obtain ⟨w1, w2, w3⟩ := wrap_spec u0 _ hu f4 (by rw [f2]; omega)
  refine ⟨f1, by rw [w1], f3, w2, by rw [f5], by rw [w3, f6], ?_⟩
  refine zero_drop_of_lt w2 ?_
  rw [w3, f6, hnd]
  exact Nat.lt_trans (Nat.mod_lt _ hvp) hvlt


theorem drs_step (db : List Nat → List Nat → List Nat → List Nat × List Nat) (hdb : DivBasicContract db)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul) (f : Nat)
    (hrec : RecOk (drs db mul (f + 1)) f) : RecOk (drs db mul (f + 1 + 1)) (f + 1) := by
  intro z u0 v0 hz0 hz hu hv h2 htop hvN hH
  have hnorm : norm v0 = v0 := normed_of_top v0 htop
  have hv0ne : v0 ≠ [] := by intro e; subst e; simp at h2
  have hvp : 0 < val v0 := by
    have := val_ge_top hv0ne htop
    have : 0 < 2 ^ 63 * 2 ^ (64 * (v0.length - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hvu := val_norm u0
  by_cases h1 : (norm u0).length = 0
  · have hres : drs db mul (f + 1 + 1) z u0 v0 = (List.replicate z.length 0, u0) := by
      unfold drs; rw [if_pos h1]
    rw [hres]
    have hn0 : norm u0 = [] := List.length_eq_zero_iff.1 h1
    have hv0 : val u0 = 0 := by rw [← hvu, hn0]; rfl
    exact conc_small2 z _ u0 u0 v0 (fun d hd => List.eq_of_mem_replicate hd) (by simp) hu rfl rfl (by omega) hv
  by_cases h3 : (norm v0).length < 40
  · have hres : drs db mul (f + 1 + 1) z u0 v0 =
        ((db z (norm u0) (norm v0)).1, (db z (norm u0) (norm v0)).2 ++ u0.drop (norm u0).length) := by
      unfold drs; rw [if_neg h1, if_pos h3]
    rw [hres, hnorm]
    exact drs_basic db hdb z u0 v0 hz0 hz hu hv h2 htop hnorm hH h1
  have h40 : 40 ≤ v0.length := by rw [hnorm] at h3; omega
  by_cases h4 : (norm u0).length < (norm v0).length
  · have hres : drs db mul (f + 1 + 1) z u0 v0 = (z, u0) := by
      unfold drs; rw [if_neg h1, if_neg h3, if_pos h4]
    rw [hres]
    rw [hnorm] at h4
    have := short_lt (norm u0) v0 (Wd_norm hu) hv hv0ne htop h4
    exact conc_small2 z z u0 u0 v0 hz0 rfl hu rfl rfl (by rw [← hvu]; exact this) hv
  · have hres : drs db mul (f + 1 + 1) z u0 v0 =
        ((finalBlock (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2)
          (drsLoop (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2) ((norm u0).length - v0.length)
            ((norm u0).length - v0.length) z (norm u0)).1
          (drsLoop (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2) ((norm u0).length - v0.length)
            ((norm u0).length - v0.length) z (norm u0)).2).1,
         (finalBlock (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2)
          (drsLoop (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2) ((norm u0).length - v0.length)
            ((norm u0).length - v0.length) z (norm u0)).1
          (drsLoop (drs db mul (f + 1)) mul v0 v0.length (v0.length / 2) ((norm u0).length - v0.length)
            ((norm u0).length - v0.length) z (norm u0)).2).2 ++ u0.drop (norm u0).length) := by
      unfold drs; rw [if_neg h1, if_neg h3, if_neg h4]; simp only [hnorm]
    rw [hres]
    exact drs_big (drs db mul (f + 1)) f hrec mul hmul z u0 v0 hz0 hz hu hv h40 htop hH (by rw [hnorm] at h4; omega)
      (by omega)

theorem drs_spec (db : List Nat → List Nat → List Nat → List Nat × List Nat) (hdb : DivBasicContract db)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul) : ∀ f : Nat, RecOk (drs db mul (f + 1)) f
  | 0 => by
    intro z u v _ _ _ _ h2 _ hvN _
    omega
  | f + 1 => drs_step db hdb mul hmul f (drs_spec db hdb mul hmul f)

/-- `DivRecursiveContract` (DivContract.lean) with the extra hypothesis `2·val u < β^len u` (the top word of `u` is `< 2^63`:
in `divLarge` it holds only the bits shifted out of `uIn`, natdiv.go:608-614).  See the report: without it the model's
`addTo(z[j-B:], qhat)` can see `len(qhat) = len(z[j-B:]) + 1`. -/
def DivRecursiveContractH (dr : List Nat → List Nat → List Nat → List Nat × List Nat) : Prop :=
  ∀ q u v : List Nat, Wd q → Wd u → Wd v → 40 ≤ v.length → 2 ^ 63 ≤ topLimb v →
    v.length ≤ u.length → q.length = u.length - v.length → 2 * val u < 2 ^ (64 * u.length) →
      (dr q u v).1.length = q.length ∧ (dr q u v).2.length = u.length ∧
      Wd (dr q u v).1 ∧ Wd (dr q u v).2 ∧
      val (dr q u v).1 = val u / val v ∧ val (dr q u v).2 = val u % val v ∧
      (∀ d ∈ (dr q u v).2.drop v.length, d = 0)

theorem divRecursive_contract (db : List Nat → List Nat → List Nat → List Nat × List Nat) (hdb : DivBasicContract db)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul) : DivRecursiveContractH (divRecursive db mul) := by
  intro q u v hq hu hv h40 htop hle hql hH
  unfold divRecursive
  have := drs_spec db hdb mul hmul v.length (List.replicate q.length 0) u v (fun d hd => List.eq_of_mem_replicate hd)
    (Wd_replicate_zero _) hu hv (by omega) htop (by omega) (by simpa [List.length_replicate, show v.length + q.length = u.length by omega] using hH)
  simpa using this

end FvModexp.Mdl
