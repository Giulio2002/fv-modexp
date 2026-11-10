import FvModexp.Proofs.Common.DivBasic
/-!
# `divLarge` (natdiv.go:597-641)

```go
func (z nat) divLarge(stk *stack, u, uIn, vIn nat) (q, r nat) {
    n := len(vIn); m := len(uIn) - n
    shift := nlz(vIn[n-1])
    v := stk.nat(n)
    u = u.make(len(uIn) + 1)
    if shift == 0 { copy(v, vIn); copy(u[:len(uIn)], uIn); u[len(uIn)] = 0 }
    else { lshVU(v, vIn, shift); u[len(uIn)] = lshVU(u[:len(uIn)], uIn, shift) }
    if alias(z, u) { z = nil }
    q = z.make(m + 1)
    if n < divRecursiveThreshold { q.divBasic(stk, u, v) } else { q.divRecursive(stk, u, v) }
    q = q.norm()
    if shift != 0 { rshVU(u, u, shift) }
    r = u.norm()
    return q, r
}
```
`divLarge dr qs uIn vIn`: `dr` is the model of `divRecursive` (assumed to satisfy `DivRecursiveContract`); `qs` is the content of `z.make(m+1)`
(arbitrary: every digit is overwritten; the theorem is for all `Wd` `qs` of length `m+1`).  The storage `u.make(len(uIn)+1)` is fully
overwritten, so its prior content is irrelevant and not modelled.

**Aliasing.** `u` may alias `uIn` exactly (same base, e.g. `x.div(.., x, ..)` with `z2 == u`): `lshVU(u[:len(uIn)], uIn, shift)` runs
`for i := n-1; i > 0; i-- { z[i] = x[i]<<s | x[i-1]>>ŝ }` top-down, reading `x[i]`, `x[i-1]` (indices ≥ the one being written... `x[i-1]`
is still unmodified) before the write of `z[i]`, so the in-place result equals the out-of-place one; `u[len(uIn)]` is outside `uIn`.
Hence the model (which computes the shifted list functionally) is exact also when `u` aliases `uIn`.
(`lshVU`'s elementwise-alias independence is the "elementwise" note in VecOps.lean.)  `v` never aliases `vIn` (`stk.nat`).
-/
namespace FvModexp.Mdl

/-- natdiv.go:597-641. Returns `(q, r)`. -/
def divLarge (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs uIn vIn : List Nat) :
    List Nat × List Nat :=
  let n := vIn.length
  let shift := nlz (vIn.getD (n - 1) 0)                                  -- nlz(vIn[n-1])
  let v := if shift = 0 then vIn else (lshVU vIn shift).1                -- copy(v, vIn) | lshVU(v, vIn, shift)
  let ul := if shift = 0 then (uIn, 0) else lshVU uIn shift              -- copy(u[:len(uIn)], uIn), 0 | lshVU(u[:len(uIn)], uIn, shift)
  let u := ul.1 ++ [ul.2]                                                -- u[len(uIn)] = ...
  let r := if n < 40 then divBasic qs u v else dr qs u v                 -- divBasic | divRecursive
  let q := norm r.1                                                      -- q = q.norm()
  let u2 := if shift ≠ 0 then (rshVU r.2 shift).1 else r.2               -- rshVU(u, u, shift)
  (q, norm u2)                                                           -- r = u.norm()

theorem val_lt_top (L : List Nat) (hL : Wd L) (hne : L ≠ []) :
    val L < (L.getD (L.length - 1) 0 + 1) * 2 ^ (64 * (L.length - 1)) := by
  induction L with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    cases ds with
    | nil => simp at *
    | cons e es =>
      have hd := Wd_cons.1 hL
      have := ih hd.2 (by simp)
      simp only [List.length_cons, Nat.add_sub_cancel] at this ⊢
      rw [val_cons d (e :: es)]
      have e1 : (d :: e :: es).getD (es.length + 1) 0 = (e :: es).getD es.length 0 := by simp
      have e2 : 64 * (es.length + 1) = 64 * es.length + 64 := by omega
      rw [e1, e2, Nat.pow_add]
      generalize (e :: es).getD es.length 0 = t at *
      generalize 2 ^ (64 * es.length) = P at *
      generalize val (e :: es) = V at *
      have h1 : 2 ^ 64 * V + 2 ^ 64 ≤ 2 ^ 64 * ((t + 1) * P) := by
        have := Nat.mul_le_mul_left (2 ^ 64) (Nat.succ_le_of_lt this)
        rw [Nat.mul_succ] at this; exact this
      have h2 : 2 ^ 64 * ((t + 1) * P) = (t + 1) * (P * 2 ^ 64) := by grind
      omega

theorem getLast_getD (L : List Nat) (hne : L ≠ []) : L.getLast?.getD 0 = L.getD (L.length - 1) 0 := by
  rw [List.getLast?_eq_some_getLast hne]
  have hl : L.length - 1 < L.length := by
    have := List.length_pos_iff.2 hne; omega
  simp only [Option.getD_some]
  rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

theorem Normed.top_ne {L : List Nat} (h : Normed L) (hne : L ≠ []) : L.getD (L.length - 1) 0 ≠ 0 := by
  induction L with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    have hh := normed_cons.1 h
    cases ds with
    | nil => have := hh.2; simp at *; omega
    | cons e es =>
      have := ih hh.1 (by simp)
      simpa using this

theorem normed_len_le {L : List Nat} (h : Normed L) (hw : Wd L) (n : Nat) (hv : val L < 2 ^ (64 * n)) : L.length ≤ n := by
  by_cases hne : L = []
  · subst hne; simp
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    have := h.val_ge hne hw
    have h2 : 2 ^ (64 * n) ≤ 2 ^ (64 * (L.length - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    omega


/-- The scaled divisor `v` (natdiv.go:608-615): same length, value `vIn * 2^shift`, top bit set. -/
theorem shift_v (vIn : List Nat) (hv : Wd vIn) (hnv : Normed vIn) (hn : vIn ≠ []) (s : Nat)
    (hs : s = nlz (vIn.getD (vIn.length - 1) 0)) :
    Wd (if s = 0 then vIn else (lshVU vIn s).1) ∧ (if s = 0 then vIn else (lshVU vIn s).1).length = vIn.length ∧
    val (if s = 0 then vIn else (lshVU vIn s).1) = val vIn * 2 ^ s ∧
    2 ^ 63 ≤ topLimb (if s = 0 then vIn else (lshVU vIn s).1) ∧ s ≤ 63 := by
  have htop0 := hnv.top_ne hn
  have htopB : vIn.getD (vIn.length - 1) 0 < 2 ^ 64 := wd_getD hv _
  obtain ⟨hs63, hs1, hs2⟩ := nlz_spec _ (Nat.pos_of_ne_zero htop0) htopB
  rw [← hs] at hs63 hs1 hs2
  have hge := val_ge_top vIn
  by_cases h0 : s = 0
  · subst h0
    simp only [if_true, Nat.pow_zero, Nat.mul_one]
    refine ⟨hv, trivial, trivial, ?_, hs63⟩
    unfold topLimb; simpa using hs2
  · rw [if_neg h0]
    have hlen : 0 < vIn.length := List.length_pos_iff.2 hn
    obtain ⟨l1, l2, l3, l4⟩ := lshVU_spec vIn s hv (by omega) hs63
    have hc : (lshVU vIn s).2 = 0 := by
      unfold lshVU
      rw [if_neg h0]
      simp only []
      rw [getLast_getD vIn hn]
      apply Nat.div_eq_of_lt
      have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
      rw [e] at hs1
      exact Nat.lt_of_mul_lt_mul_right hs1
    rw [hc] at l4
    simp only [Nat.mul_zero, Nat.add_zero] at l4
    refine ⟨l2, by rw [l1], l4, ?_, hs63⟩
    have hne1 : (lshVU vIn s).1 ≠ [] := by
      intro h; rw [h] at l1; simp at l1; omega
    have h1 := val_lt_top _ l2 hne1
    rw [l1] at h1
    unfold topLimb
    rw [l1]
    rw [l4] at h1
    have h2 : 2 ^ 63 * 2 ^ (64 * (vIn.length - 1)) ≤ val vIn * 2 ^ s := by
      have a1 : vIn.getD (vIn.length - 1) 0 * 2 ^ (64 * (vIn.length - 1)) * 2 ^ s ≤ val vIn * 2 ^ s :=
        Nat.mul_le_mul_right _ hge
      have a2 : 2 ^ 63 * 2 ^ (64 * (vIn.length - 1)) ≤ vIn.getD (vIn.length - 1) 0 * 2 ^ s * 2 ^ (64 * (vIn.length - 1)) :=
        Nat.mul_le_mul_right _ hs2
      have a3 : vIn.getD (vIn.length - 1) 0 * 2 ^ s * 2 ^ (64 * (vIn.length - 1)) =
          vIn.getD (vIn.length - 1) 0 * 2 ^ (64 * (vIn.length - 1)) * 2 ^ s := by grind
      omega
    have h3 : 2 ^ 63 * 2 ^ (64 * (vIn.length - 1)) < ((lshVU vIn s).1.getD ((lshVU vIn s).1.length - 1) 0 + 1) *
        2 ^ (64 * (vIn.length - 1)) := by
      rw [l1]; omega
    have := Nat.lt_of_mul_lt_mul_right h3
    rw [l1] at this
    omega

/-- The scaled dividend (natdiv.go:616-621). -/
theorem shift_u (uIn : List Nat) (hu : Wd uIn) (s : Nat) (hs : s ≤ 63) :
    Wd ((if s = 0 then (uIn, 0) else lshVU uIn s).1 ++ [(if s = 0 then (uIn, 0) else lshVU uIn s).2]) ∧
    ((if s = 0 then (uIn, 0) else lshVU uIn s).1 ++ [(if s = 0 then (uIn, 0) else lshVU uIn s).2]).length = uIn.length + 1 ∧
    val ((if s = 0 then (uIn, 0) else lshVU uIn s).1 ++ [(if s = 0 then (uIn, 0) else lshVU uIn s).2]) = val uIn * 2 ^ s := by
  by_cases h0 : s = 0
  · subst h0
    simp only [if_true, Nat.pow_zero, Nat.mul_one]
    refine ⟨Wd_append.2 ⟨hu, by intro d hd; simp at hd; subst hd; decide⟩, by simp, ?_⟩
    rw [val_append]; simp
  · rw [if_neg h0]
    obtain ⟨l1, l2, l3, l4⟩ := lshVU_spec uIn s hu (by omega) hs
    refine ⟨Wd_append.2 ⟨l2, by intro d hd; simp at hd; subst hd; exact l3⟩, by simp [l1], ?_⟩
    rw [val_append, l1]; simp only [val_cons, val_nil]; omega


/-- Correctness of `divLarge`: with `dr` satisfying the `divRecursive` contract, `q = ⌊uIn/vIn⌋`, `r = uIn % vIn`, both normalised.
Inputs: `vIn` normalised (the Go callers pass normalised nats), `len vIn ≥ 2`, `len uIn ≥ len vIn`; `qs` = `z.make(m+1)` (any content). -/
theorem divLarge_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs uIn vIn : List Nat) (hqs : Wd qs) (hqsl : qs.length = uIn.length - vIn.length + 1)
    (hu : Wd uIn) (hv : Wd vIn) (hnv : Normed vIn) (hn : 2 ≤ vIn.length) (hle : vIn.length ≤ uIn.length) :
    Wd (divLarge dr qs uIn vIn).1 ∧ Wd (divLarge dr qs uIn vIn).2 ∧
    val (divLarge dr qs uIn vIn).1 = val uIn / val vIn ∧ val (divLarge dr qs uIn vIn).2 = val uIn % val vIn ∧
    Normed (divLarge dr qs uIn vIn).1 ∧ Normed (divLarge dr qs uIn vIn).2 ∧
    (divLarge dr qs uIn vIn).1.length ≤ uIn.length - vIn.length + 1 ∧ (divLarge dr qs uIn vIn).2.length ≤ vIn.length := by
  have hne : vIn ≠ [] := by intro h; subst h; simp at hn
  have htop0 := hnv.top_ne hne
  have hge := val_ge_top vIn
  have hDge : 2 ^ (64 * (vIn.length - 1)) ≤ val vIn := by
    have := hnv.val_ge hne hv; exact this
  have hD0 : 0 < val vIn := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hDge
  unfold divLarge
  dsimp only
  generalize hs : nlz (vIn.getD (vIn.length - 1) 0) = s
  obtain ⟨v1, v2, v3, v4, v5⟩ := shift_v vIn hv hnv hne s hs.symm
  obtain ⟨u1, u2, u3⟩ := shift_u uIn hu s v5
  generalize (if s = 0 then vIn else (lshVU vIn s).1) = v at *
  generalize (if s = 0 then (uIn, 0) else lshVU uIn s).1 ++ [(if s = 0 then (uIn, 0) else lshVU uIn s).2] = u at *
  have hD : 0 < val v := by rw [v3]; exact Nat.mul_pos hD0 (Nat.two_pow_pos _)
  -- the common hypotheses of both division routines
  have hlt : val u < val v * 2 ^ (64 * qs.length) := by
    have e1 : val uIn < 2 ^ (64 * uIn.length) := val_lt hu
    have e2 : 2 ^ (64 * (uIn.length - vIn.length + 1)) * 2 ^ (64 * (vIn.length - 1)) = 2 ^ (64 * uIn.length) := by
      rw [← Nat.pow_add]; congr 1; omega
    have e3 : 2 ^ (64 * qs.length) * 2 ^ (64 * (vIn.length - 1)) ≤ val vIn * 2 ^ (64 * qs.length) := by
      rw [Nat.mul_comm (val vIn)]; exact Nat.mul_le_mul_left _ hDge
    rw [u3, v3, hqsl]
    have : val uIn < val vIn * 2 ^ (64 * (uIn.length - vIn.length + 1)) := by
      rw [hqsl] at e3; omega
    have := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos s)
    calc val uIn * 2 ^ s < val vIn * 2 ^ (64 * (uIn.length - vIn.length + 1)) * 2 ^ s := this
      _ = val vIn * 2 ^ s * 2 ^ (64 * (uIn.length - vIn.length + 1)) := by grind
  have hulen : u.length - v.length = qs.length := by omega
  have hquo : val u / val v = val uIn / val vIn := by rw [u3, v3]; exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)
  have hrem : val u % val v = (val uIn % val vIn) * 2 ^ s := by
    rw [u3, v3]; exact Nat.mul_mod_mul_right _ _ _
  -- the division step
  have key : ∃ q' u', Wd q' ∧ Wd u' ∧ q'.length = qs.length ∧ u'.length = u.length ∧ val q' = val uIn / val vIn ∧
      val u' = (val uIn % val vIn) * 2 ^ s ∧
      (if vIn.length < 40 then divBasic qs u v else dr qs u v) = (q', u') := by
    by_cases h40 : vIn.length < 40
    · have hc := divBasic_contract qs u v hqs u1 v1 (by omega) v4
      obtain ⟨_, hc2⟩ := hc
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc2 (by omega) (Or.inr ⟨hulen, hlt⟩)
      refine ⟨(divBasic qs u v).1, (divBasic qs u v).2, c3, c4, c1, c2, ?_, ?_, by rw [if_pos h40]⟩
      · rw [← hquo, ← c5, List.take_of_length_le (by omega)]
      · rw [← hrem]; exact c7
    · have hc := hdr qs u v hqs u1 v1 (by omega) v4 (by omega) hulen.symm hlt
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
      refine ⟨(dr qs u v).1, (dr qs u v).2, c3, c4, c1, c2, ?_, ?_, by rw [if_neg h40]⟩
      · rw [← hquo]; exact c5
      · rw [← hrem]; exact c6
  obtain ⟨q', u', k1, k2, k3, k4, k5, k6, k7⟩ := key
  rw [k7]
  dsimp only
  have hmod : val uIn % val vIn < val vIn := Nat.mod_lt _ hD0
  have hu2 : Wd (if s ≠ 0 then (rshVU u' s).1 else u') ∧
      val (if s ≠ 0 then (rshVU u' s).1 else u') = val uIn % val vIn := by
    by_cases h0 : s = 0
    · subst h0
      simp only [ne_eq, not_true_eq_false, ite_false]
      exact ⟨k2, by rw [k6]; simp⟩
    · simp only [h0, ne_eq, not_false_eq_true, ite_true]
      refine ⟨(rshVU_spec u' s k2 (by omega) v5).2.1, ?_⟩
      rw [(rshVU_spec u' s k2 (by omega) v5).2.2.1, k6]
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos s)
  generalize (if s ≠ 0 then (rshVU u' s).1 else u') = u2 at *
  obtain ⟨hw2, hv2⟩ := hu2
  have hmodv : val u2 < 2 ^ (64 * vIn.length) := by
    have := val_lt hv; omega
  refine ⟨Wd_norm k1, Wd_norm hw2, by rw [val_norm, k5], by rw [val_norm, hv2], normed_norm _, normed_norm _, ?_, ?_⟩
  · exact Nat.le_trans (length_norm_le _) (by omega)
  · exact normed_len_le (normed_norm _) (Wd_norm hw2) _ (by rw [val_norm]; exact hmodv)

end FvModexp.Mdl
