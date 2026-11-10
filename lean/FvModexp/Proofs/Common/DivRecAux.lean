import FvModexp.Proofs.Common.Slices
import FvModexp.Proofs.Common.DivContract
/-!
# Auxiliary list lemmas for the recursive division model (natdiv.go:740-892)

* `natCmp_stale`: `nat.cmp` (nat.go:152) compares *lengths first*; `qhatv` in `divRecursiveStep` is not renormalised after the
  correction `qhatv -= v[:s]`.  The comparison is still correct when either the left operand is normalised or its length is at most
  the length of the (normalised) right operand.
* `subToC`: `subVV(z[:n], z[:n], x); if c > 0 { c = subVW(z[n:], z[n:], c) }` (natdiv.go:882-886) and its spec (no borrow out when `x <= z`).
* limb lemmas: zero limbs above a bound, normalised length bounds, top-limb lower bound.
-/
namespace FvModexp.Mdl

/-! ### limb bounds -/

theorem zero_drop_of_lt {l : List Nat} (h : Wd l) {k : Nat} (hk : val l < 2 ^ (64 * k)) : ∀ d ∈ l.drop k, d = 0 := by
  have := (val_take_mod l k h).2
  rw [Nat.div_eq_of_lt hk] at this
  exact val_eq_zero_iff.1 this

theorem length_le_of_normed {l : List Nat} (h : Wd l) (hn : Normed l) {k : Nat} (hk : val l < 2 ^ (64 * k)) :
    l.length ≤ k := by
  by_cases hl : l = []
  · subst hl; simp
  · have := hn.val_ge hl h
    have h2 : 2 ^ (64 * (l.length - 1)) < 2 ^ (64 * k) := Nat.lt_of_le_of_lt this hk
    have h3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h2
    have : l.length ≠ 0 := fun e => hl (List.length_eq_zero_iff.1 e)
    omega

theorem lt_length_norm {l : List Nat} (h : Wd l) {k : Nat} (hk : 2 ^ (64 * k) ≤ val l) : k < (norm l).length := by
  refine Nat.lt_of_not_ge ?_
  intro hc
  have h1 := val_lt (Wd_norm h)
  rw [val_norm] at h1
  have : 2 ^ (64 * (norm l).length) ≤ 2 ^ (64 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem lt_length_norm' {l : List Nat} (h : Wd l) {k : Nat} (hk : 2 ^ (64 * k) ≤ val l) : k + 1 ≤ (norm l).length :=
  lt_length_norm h hk

/-- The top limb of a non-empty list gives a lower bound on the value. -/
theorem topLimb_mul_le_val : ∀ (l : List Nat), l ≠ [] → topLimb l * 2 ^ (64 * (l.length - 1)) ≤ val l
  | [], h => absurd rfl h
  | [d], _ => by simp [topLimb, val]
  | d :: e :: es, _ => by
    have ih := topLimb_mul_le_val (e :: es) (by simp)
    have ht : topLimb (d :: e :: es) = topLimb (e :: es) := by simp [topLimb]
    rw [ht]
    simp only [List.length_cons, val_cons] at ih ⊢
    have e1 : 64 * (es.length + 1 + 1 - 1) = 64 + 64 * (es.length + 1 - 1) := by omega
    rw [e1, Nat.pow_add]
    have := Nat.mul_le_mul_left (2 ^ 64) ih
    generalize topLimb (e :: es) = T at *
    generalize 2 ^ (64 * (es.length + 1 - 1)) = P at *
    have e2 : T * (2 ^ 64 * P) = 2 ^ 64 * (T * P) := by rw [Nat.mul_left_comm]
    rw [e2]
    omega

theorem val_ge_top63 {l : List Nat} (hne : l ≠ []) (h : 2 ^ 63 ≤ topLimb l) :
    2 ^ 63 * 2 ^ (64 * (l.length - 1)) ≤ val l :=
  Nat.le_trans (Nat.mul_le_mul_right _ h) (topLimb_mul_le_val l hne)

/-! ### nat.cmp on a stale-length left operand -/

theorem natCmp_stale (x y : List Nat) (hx : Wd x) (hy : Wd y) (hny : Normed y)
    (h : Normed x ∨ x.length ≤ y.length) : natCmp x y = cmpInt (val x) (val y) := by
  rcases h with hnx | hl
  · exact natCmp_spec x y hx hy hnx hny
  · rcases Nat.lt_or_ge x.length y.length with hlt | hge
    · have hyne : y ≠ [] := by intro e; rw [e] at hlt; simp at hlt
      have h2 := hny.val_ge hyne hy
      have h1 := val_lt hx
      have : 2 ^ (64 * x.length) ≤ 2 ^ (64 * (y.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      unfold natCmp
      rw [if_pos (Or.inl (by omega)), if_pos hlt, cmpInt_lt (by omega)]
    · have he : x.length = y.length := by omega
      by_cases h0 : x.length = 0
      · have hx0 : x = [] := List.length_eq_zero_iff.1 h0
        have hy0 : y = [] := List.length_eq_zero_iff.1 (by omega)
        subst hx0; subst hy0; simp [natCmp, cmpInt]
      · unfold natCmp
        rw [if_neg (by omega)]
        have hxne : x ≠ [] := fun e => h0 (by rw [e]; rfl)
        rw [cmpRev_spec x.reverse y.reverse (fun d hd => hx d (List.mem_reverse.1 hd))
          (fun d hd => hy d (List.mem_reverse.1 hd)) (by simp [he]) (by simpa using hxne), ← val_reverse, ← val_reverse]
        simp

/-! ### z[:n] -= x with borrow propagation -/

/-- `subVV(z[:n], z[:n], x); if c > 0 { c = subVW(z[n:], z[n:], c) }`; returns the new `z` and the final borrow
(natdiv.go:882-886; the first block at natdiv.go:827-830 ignores the borrow). -/
def subToC (z x : List Nat) : List Nat × Nat :=
  let r := subVV (z.take x.length) x
  if r.2 > 0 then (let t := subVW (z.drop x.length) r.2; (r.1 ++ t.1, t.2)) else (r.1 ++ z.drop x.length, 0)

theorem sub_chain_nat (P Q a b lo lo2 vx c c2 : Nat) (hc : c ≤ 1) (hlo : lo < P) (hlo2 : lo2 < Q)
    (h1 : lo + vx = a + P * c) (h2 : lo2 + c = b + Q * c2) (hle : vx ≤ a + P * b) : c2 = 0 := by
  rcases Nat.eq_zero_or_pos c2 with h | h
  · exact h
  · exfalso
    have hq : Q ≤ Q * c2 := Nat.le_mul_of_pos_right _ h
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0; omega
    · have hc1 : c = 1 := by omega
      subst hc1
      have hb : b = 0 := by omega
      subst hb
      simp only [Nat.mul_zero, Nat.mul_one] at *
      omega

theorem subToC_spec (z x : List Nat) (hz : Wd z) (hx : Wd x) (hl : x.length ≤ z.length) (hle : val x ≤ val z) :
    (subToC z x).1.length = z.length ∧ Wd (subToC z x).1 ∧ (subToC z x).2 = 0 ∧
    val (subToC z x).1 + val x = val z := by
  unfold subToC
  simp only []
  have hlen : (z.take x.length).length = x.length := by simp; omega
  obtain ⟨i1, i2, i3, i4⟩ := subVVc_spec (z.take x.length) x 0 (hz.take _) hx hlen (by omega)
  have hzs := take_len_drop_val z x.length hl
  have hlo : (subVV (z.take x.length) x).1.length = x.length := by unfold subVV; rw [i1, hlen]
  have hwlo : Wd (subVV (z.take x.length) x).1 := i2
  have hc1 : (subVV (z.take x.length) x).2 ≤ 1 := i3
  have hsum : val (subVV (z.take x.length) x).1 + val x = val (z.take x.length) +
      2 ^ (64 * x.length) * (subVV (z.take x.length) x).2 := by
    unfold subVV; rw [hlen] at i4; omega
  have hlolt : val (subVV (z.take x.length) x).1 < 2 ^ (64 * x.length) := by
    have := val_lt hwlo; rwa [hlo] at this
  have hdl : (z.drop x.length).length = z.length - x.length := by simp
  generalize (subVV (z.take x.length) x).1 = lo at *
  generalize (subVV (z.take x.length) x).2 = c at *
  by_cases hc : c > 0
  · rw [if_pos hc]
    have hzd : (z.drop x.length) ≠ [] := by
      intro e
      have hnz : x.length = z.length := by
        have := congrArg List.length e; simp at this; omega
      have htk : z.take x.length = z := by rw [hnz]; exact List.take_length
      have hv0 : val (z.drop x.length) = 0 := by rw [e]; rfl
      rw [hv0] at hzs
      rw [htk] at hsum
      have hh : 2 ^ (64 * x.length) ≤ 2 ^ (64 * x.length) * c := Nat.le_mul_of_pos_right _ hc
      omega
    obtain ⟨j1, j2, j3, j4, j5⟩ := subVW_spec (z.drop x.length) c (hz.drop _) (by omega)
    rw [hdl] at j1 j5
    have hlo2 : val (subVW (z.drop x.length) c).1 < 2 ^ (64 * (z.length - x.length)) := by
      have := val_lt j2; rwa [j1] at this
    have hb2 : (subVW (z.drop x.length) c).2 = 0 :=
      sub_chain_nat _ _ (val (z.take x.length)) (val (z.drop x.length)) _ _ (val x) c _ hc1 hlolt hlo2 hsum j5
        (by
          have : val (z.take x.length) + 2 ^ (64 * x.length) * val (z.drop x.length) = val z := hzs.symm
          omega)
    refine ⟨by simp [hlo, j1, hdl]; omega, Wd_append.2 ⟨hwlo, j2⟩, hb2, ?_⟩
    rw [val_append, hlo]
    rw [hb2] at j5
    simp only [Nat.mul_zero, Nat.add_zero] at j5
    have hP := congrArg (fun t => 2 ^ (64 * x.length) * t) j5
    simp only [Nat.mul_add] at hP
    omega
  · rw [if_neg hc]
    have hc0 : c = 0 := by omega
    subst hc0
    refine ⟨by simp [hlo, hdl]; omega, Wd_append.2 ⟨hwlo, hz.drop _⟩, rfl, ?_⟩
    rw [val_append, hlo]
    omega

end FvModexp.Mdl
