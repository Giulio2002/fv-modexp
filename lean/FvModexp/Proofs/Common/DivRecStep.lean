import FvModexp.Proofs.Common.DivRecMath
/-!
# One wide-digit refinement of `divRecursiveStep` (natdiv.go:777-892): model and spec

State `St = (qhat, qhatv-buffer, uu)`.  `qhatv` is `stk.nat(3n)` cleared, then `qhatv = qhatv.mul(stk, qhat, v[:s])`: a slice of
the 3n-limb backing buffer whose *length* `ql` is the length of the (normalised) product and whose capacity (the buffer) is
zero beyond the product.  The correction `qhatv -= v[:s]` (natdiv.go:812-814) runs on the buffer without renormalising.
-/
namespace FvModexp.Mdl

structure St where
  qhat : List Nat
  buf : List Nat
  w : List Nat

/-- `subVV(qhatv[:s], qhatv[:s], v[:s]); if len(qhatv) > s { subVW(qhatv[s:], qhatv[s:], c) }` (natdiv.go:812-814, 868-870),
on the backing buffer (`ql = len(qhatv)`). -/
def corrSub (buf v0 : List Nat) (s ql : Nat) : List Nat :=
  let r := subVV (buf.take s) v0
  let b1 := r.1 ++ buf.drop s
  if s < ql then upd b1 s (subVW (sl b1 s (ql - s)) r.2).1 else b1

/-- One correction (loop body natdiv.go:807-816 / 863-872): `qhat--`, `qhatv -= v[:s]`, `uu[s:] += v[s:]`. -/
def corrOnce (v : List Nat) (s ql : Nat) (st : St) : St :=
  { qhat := (subVW st.qhat 1).1
    buf := corrSub st.buf (v.take s) s ql
    w := upd st.w s (addTo (st.w.drop s) (v.drop s)) }

/-- `qhatv.cmp(uu.norm())` with `qhatv = buf[:ql]`. -/
def cmpQ (ql : Nat) (st : St) : Int := natCmp (st.buf.take ql) (norm st.w)

/-- First block (natdiv.go:805-816): `for i := 0; i < 2; i++ { e := cmp; if e <= 0 { break }; ...correct... }`. -/
def corr1 (v : List Nat) (s ql : Nat) : Nat → St → St
  | 0, st => st
  | i + 1, st => if cmpQ ql st ≤ 0 then st else corr1 v s ql i (corrOnce v s ql st)

/-- Final block (natdiv.go:861-872): `for i := 0; i < 2; i++ { if e := cmp; e > 0 { ...correct... } }`. -/
def corr2 (v : List Nat) (s ql : Nat) : Nat → St → St
  | 0, st => st
  | i + 1, st => corr2 v s ql i (if cmpQ ql st > 0 then corrOnce v s ql st else st)

theorem corr2_eq_corr1 (v : List Nat) (s ql : Nat) : ∀ (i : Nat) (st : St), corr2 v s ql i st = corr1 v s ql i st
  | 0, st => rfl
  | i + 1, st => by
    by_cases h : cmpQ ql st > 0
    · simp only [corr2, corr1, if_pos h, Int.not_le.2 h, if_false]; exact corr2_eq_corr1 v s ql i _
    · have h' : cmpQ ql st ≤ 0 := Int.not_lt.1 h
      simp only [corr2, corr1, if_neg h, if_pos h']
      rw [corr2_eq_corr1 v s ql i st]
      cases i with
      | zero => rfl
      | succ i => simp only [corr1, if_pos h']

structure RM where
  q : List Nat
  w : List Nat
  c : Nat
  e : Int

/-- Common part of both blocks (natdiv.go:797-834 / 853-889), starting from `qhat = qhat.norm()` and `uu` already holding the
remainder `r̂` in `uu[s:]`: product `qhatv`, ≤ 2 corrections (`blk2` selects the loop shape), the `panic("impossible")` test (`e`), and the
subtraction `uu -= qhatv` (`c` = final borrow).  `mul` is the multiplier callee (`qhatv.mul(stk, qhat, v[:s])`). -/
def refMid (mul : List Nat → List Nat → List Nat) (blk2 : Bool) (v : List Nat) (n s : Nat) (qhat w : List Nat) : RM :=
  let p := mul qhat (v.take s)
  let ql := p.length
  let st := (if blk2 then corr2 v s ql 2 else corr1 v s ql 2) { qhat := qhat, buf := p ++ List.replicate (3 * n - ql) 0, w := w }
  let r := subToC st.w (st.buf.take ql)
  { q := st.qhat, w := r.1, c := r.2, e := cmpQ ql st }

/-! ### upd helpers -/

theorem upd_eq_of_full (z l : List Nat) (i : Nat) (hi : i ≤ z.length) (hl : l.length = z.length - i) :
    upd z i l = z.take i ++ l := by
  unfold upd
  rw [List.drop_of_length_le (by omega)]; simp

theorem val_upd_full (z l : List Nat) (i : Nat) (hi : i ≤ z.length) (hl : l.length = z.length - i) :
    val (upd z i l) = val (z.take i) + 2 ^ (64 * i) * val l := by
  rw [upd_eq_of_full z l i hi hl, val_append]
  have : (z.take i).length = i := by simp; omega
  rw [this]

theorem length_upd_full (z l : List Nat) (i : Nat) (hi : i ≤ z.length) (hl : l.length = z.length - i) :
    (upd z i l).length = z.length := by
  rw [upd_eq_of_full z l i hi hl]; simp; omega

/-! ### corrSub -/

theorem corrSub_spec (buf v0 : List Nat) (s ql : Nat) (hb : Wd buf) (hv : Wd v0) (hvl : v0.length = s)
    (hs : s ≤ buf.length) (hq : ql ≤ buf.length) (hlt : val buf < 2 ^ (64 * ql)) (hle : val v0 ≤ val buf) :
    (corrSub buf v0 s ql).length = buf.length ∧ Wd (corrSub buf v0 s ql) ∧
    val (corrSub buf v0 s ql) + val v0 = val buf := by
  unfold corrSub
  simp only []
  have hlen : (buf.take s).length = s := by simp; omega
  obtain ⟨i1, i2, i3, i4⟩ := subVVc_spec (buf.take s) v0 0 (hb.take _) hv (by omega) (by omega)
  have hr1 : (subVV (buf.take s) v0).1.length = s := by unfold subVV; rw [i1, hlen]
  have hwr : Wd (subVV (buf.take s) v0).1 := i2
  have hc1 : (subVV (buf.take s) v0).2 ≤ 1 := i3
  have hsum : val (subVV (buf.take s) v0).1 + val v0 = val (buf.take s) + 2 ^ (64 * s) * (subVV (buf.take s) v0).2 := by
    unfold subVV; rw [hlen] at i4; omega
  have hrlt : val (subVV (buf.take s) v0).1 < 2 ^ (64 * s) := by
    have := val_lt hwr; rwa [hr1] at this
  generalize (subVV (buf.take s) v0).1 = r1 at *
  generalize (subVV (buf.take s) v0).2 = c at *
  have hzt : val (buf.drop ql) = 0 := by
    have := (val_take_mod buf ql hb).2; rwa [Nat.div_eq_of_lt hlt] at this
  have hbs := take_len_drop_val buf s hs
  by_cases hsq : s < ql
  · rw [if_pos hsq]
    have hdrop : (r1 ++ buf.drop s).drop s = buf.drop s := List.drop_left' hr1
    have hsl : sl (r1 ++ buf.drop s) s (ql - s) = (buf.drop s).take (ql - s) := by unfold sl; rw [hdrop]
    rw [hsl]
    obtain ⟨mid, hmid⟩ : ∃ mid, mid = (buf.drop s).take (ql - s) := ⟨_, rfl⟩
    rw [← hmid]
    have hmidl : mid.length = ql - s := by simp [hmid]; omega
    have hmw : Wd mid := by rw [hmid]; exact (hb.drop s).take _
    obtain ⟨j1, j2, j3, j4, j5⟩ := subVW_spec mid c hmw (by omega)
    rw [hmidl] at j1 j5
    have hbd : buf.drop s = mid ++ buf.drop ql := by
      have := List.take_append_drop (ql - s) (buf.drop s)
      rw [List.drop_drop, show s + (ql - s) = ql by omega, ← hmid] at this
      exact this.symm
    have hvmid : val (buf.drop s) = val mid := by rw [hbd, val_append, hzt]; simp
    have hlo2 : val (subVW mid c).1 < 2 ^ (64 * (ql - s)) := by
      have := val_lt j2; rwa [j1] at this
    have hb2 : (subVW mid c).2 = 0 :=
      sub_chain_nat _ _ (val (buf.take s)) (val mid) _ _ (val v0) c _ hc1 hrlt hlo2 hsum j5
        (by have := hbs; rw [hvmid] at this; omega)
    rw [hb2] at j5
    simp only [Nat.mul_zero, Nat.add_zero] at j5
    have h1 : (subVW mid c).1.length + s ≤ (r1 ++ buf.drop s).length := by
      simp [j1, hr1]; omega
    have hu := val_upd (r1 ++ buf.drop s) (subVW mid c).1 s (by omega)
    rw [hdrop, j1] at hu
    have hu2 : (buf.drop s).take (ql - s) = mid := hmid.symm
    rw [hu2] at hu
    refine ⟨?_, Wd_upd (Wd_append.2 ⟨hwr, hb.drop s⟩) j2, ?_⟩
    · rw [length_upd _ _ _ (by omega)]; simp [hr1]; omega
    · rw [val_append, hr1, hvmid] at hu
      have hP := congrArg (fun t => 2 ^ (64 * s) * t) j5
      simp only [Nat.mul_add] at hP
      have hbs' := hbs; rw [hvmid] at hbs'
      omega
  · rw [if_neg hsq]
    have hp : 2 ^ (64 * ql) ≤ 2 ^ (64 * s) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz2 : val (buf.drop s) = 0 := by
      have := (val_take_mod buf s hb).2; rwa [Nat.div_eq_of_lt (by omega)] at this
    have hc0 : c = 0 := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exact h
      · exfalso
        have : 2 ^ (64 * s) ≤ 2 ^ (64 * s) * c := Nat.le_mul_of_pos_right _ h
        rw [hz2] at hbs; simp at hbs; omega
    subst hc0
    refine ⟨by simp [hr1]; omega, Wd_append.2 ⟨hwr, hb.drop s⟩, ?_⟩
    rw [val_append, hr1, hz2]; rw [hz2] at hbs; simp at hbs ⊢; omega


/-! ### the context of one refinement -/

/-- `v[s:]·β^s` as a number. -/
def v1S (v : List Nat) (s : Nat) : Nat := val (v.drop s) * 2 ^ (64 * s)

structure Ctx (v : List Nat) (n s B ql L : Nat) : Prop where
  hv : Wd v
  hn : v.length = n
  htop : 2 ^ 63 ≤ topLimb v
  hsB : s + 1 = B
  h2B : 2 * B ≤ n
  hqln : ql ≤ n
  hLn : n ≤ L

theorem topLimb_drop (v : List Nat) (s : Nat) (h : s < v.length) : topLimb (v.drop s) = topLimb v := by
  unfold topLimb
  have h1 : (v.drop s).length - 1 = (v.length - 1) - s := by simp; omega
  rw [h1]
  have h2 : s + (v.length - 1 - s) = v.length - 1 := by omega
  have h3 : (v.length - 1) < v.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, h2]

theorem Ctx.s_lt {v n s B ql L} (c : Ctx v n s B ql L) : s < n := by have := c.hsB; have := c.h2B; omega

theorem Ctx.v_split {v n s B ql L} (c : Ctx v n s B ql L) : val v = val (v.take s) + v1S v s := by
  have := val_split v s (by have := c.hn; have := c.s_lt; omega)
  unfold v1S; rw [this, Nat.mul_comm (val (v.drop s))]

theorem Ctx.v1S_ge {v n s B ql L} (c : Ctx v n s B ql L) : 2 ^ 63 * 2 ^ (64 * (n - 1)) ≤ v1S v s := by
  have hs := c.s_lt
  have hne : v.drop s ≠ [] := by
    intro e; have := congrArg List.length e; simp at this; have := c.hn; omega
  have h := val_ge_top63 hne (by rw [topLimb_drop v s (by have := c.hn; omega)]; exact c.htop)
  have hl : (v.drop s).length - 1 = n - s - 1 := by simp; have := c.hn; omega
  rw [hl] at h
  unfold v1S
  have := Nat.mul_le_mul_right (2 ^ (64 * s)) h
  have e : 2 ^ 63 * 2 ^ (64 * (n - s - 1)) * 2 ^ (64 * s) = 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  omega

theorem Ctx.v0_wd {v n s B ql L} (c : Ctx v n s B ql L) : Wd (v.take s) ∧ (v.take s).length = s ∧ Wd (v.drop s) ∧
    (v.drop s).length = n - s := by
  have := c.s_lt
  refine ⟨c.hv.take _, by simp [c.hn]; omega, c.hv.drop _, by simp [c.hn]⟩

/-- Invariant of the correction loop after `k` corrections (`qh` = initial `val qhat`, `Y` = initial `val uu`). -/
def Inv (v : List Nat) (n s ql L lq qh Y k : Nat) (st : St) : Prop :=
  Wd st.qhat ∧ Wd st.buf ∧ Wd st.w ∧ st.qhat.length = lq ∧ st.buf.length = 3 * n ∧ st.w.length = L ∧
  val st.qhat + k = qh ∧ val st.buf = val st.qhat * val (v.take s) ∧ val st.w = Y + k * v1S v s ∧
  val st.buf < 2 ^ (64 * ql) ∧ (Normed (st.buf.take ql) ∨ ql ≤ (norm st.w).length)

theorem corrOnce_inv {v n s B ql L} (c : Ctx v n s B ql L) (lq qh Y X k : Nat) (st : St)
    (hI : Inv v n s ql L lq qh Y k st) (hX : X = qh * v1S v s + Y) (hXL : X < 2 ^ (64 * L))
    (hq1 : 1 ≤ val st.qhat) : Inv v n s ql L lq qh Y (k + 1) (corrOnce v s ql st) := by
  obtain ⟨hwq, hwb, hww, hlq, hbl, hwl, hk, hbv, hwv, hblt, hnorm⟩ := hI
  have hs := c.s_lt
  have hn := c.hn
  obtain ⟨hw0, hl0, hw1, hl1⟩ := c.v0_wd
  have hv1ge := c.v1S_ge
  have hq3 := c.hqln
  have hLn := c.hLn
  -- qhat--
  have hqne : st.qhat ≠ [] := by intro e; rw [e] at hq1; simp at hq1
  obtain ⟨a1, a2, a3, a4, a5⟩ := subVW_spec st.qhat 1 hwq (by decide)
  have hbor : (subVW st.qhat 1).2 = 0 := by
    have h3 := a3 hqne
    have h4 := val_lt a2
    rw [a1] at h4
    rcases Nat.eq_zero_or_pos (subVW st.qhat 1).2 with h | h
    · exact h
    · exfalso
      have : 2 ^ (64 * st.qhat.length) ≤ 2 ^ (64 * st.qhat.length) * (subVW st.qhat 1).2 := Nat.le_mul_of_pos_right _ h
      omega
  rw [hbor] at a5
  simp only [Nat.mul_zero, Nat.add_zero] at a5
  -- buffer
  have hbge : val (v.take s) ≤ val st.buf := by
    rw [hbv]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨b1, b2, b3⟩ := corrSub_spec st.buf (v.take s) s ql hwb hw0 hl0 (by omega) (by omega) hblt hbge
  -- uu += v[s:]
  have hwdrop : (st.w.drop s).length = L - s := by simp [hwl]
  have hsplit := val_split st.w s (by omega)
  have hv1ge' := hv1ge
  have hv1lt : val (v.drop s) + val (st.w.drop s) < 2 ^ (64 * (st.w.drop s).length) := by
    rw [hwdrop]
    have e : 2 ^ (64 * L) = 2 ^ (64 * s) * 2 ^ (64 * (L - s)) := by rw [← Nat.pow_add, ← Nat.mul_add]; congr 2; omega
    rw [e] at hXL
    unfold v1S at hwv hX hv1ge
    have hkq : qh = val st.qhat + k := by omega
    have hqq : val (v.drop s) * 2 ^ (64 * s) ≤ val st.qhat * (val (v.drop s) * 2 ^ (64 * s)) := Nat.le_mul_of_pos_left _ hq1
    have hX2 : X = val st.qhat * (val (v.drop s) * 2 ^ (64 * s)) + val st.w := by
      rw [hwv, hX, hkq, Nat.add_mul]; omega
    have : 2 ^ (64 * s) * (val (v.drop s) + val (st.w.drop s)) < 2 ^ (64 * s) * 2 ^ (64 * (L - s)) := by
      rw [Nat.mul_add, Nat.mul_comm (2 ^ (64 * s)) (val (v.drop s))]
      have := hsplit
      generalize val (v.drop s) * 2 ^ (64 * s) = A at *
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨c1, c2, c3⟩ := addTo_spec (st.w.drop s) (v.drop s) (hww.drop s) hw1 (by rw [hwdrop, hl1]; omega) (by omega)
  have hupl : (addTo (st.w.drop s) (v.drop s)).length = L - s := by rw [c1, hwdrop]
  have hu := val_upd_full st.w (addTo (st.w.drop s) (v.drop s)) s (by omega) (by rw [hupl, hwl])
  have hwl' : (upd st.w s (addTo (st.w.drop s) (v.drop s))).length = L := by
    rw [length_upd_full _ _ _ (by omega) (by rw [hupl, hwl])]; exact hwl
  have hww' : Wd (upd st.w s (addTo (st.w.drop s) (v.drop s))) := Wd_upd hww c2
  have hvw' : val (upd st.w s (addTo (st.w.drop s) (v.drop s))) = val st.w + v1S v s := by
    rw [hu, c3]
    have := hsplit
    unfold v1S; rw [Nat.mul_add, Nat.mul_comm (2 ^ (64 * s)) (val (v.drop s))]
    omega
  refine ⟨a2, b2, hww', by show (subVW st.qhat 1).1.length = lq; rw [a1, hlq], by show (corrSub st.buf (v.take s) s ql).length = 3 * n; rw [b1, hbl], hwl', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [corrOnce]; omega
  · simp only [corrOnce]
    have e0 : val (subVW st.qhat 1).1 = val st.qhat - 1 := by omega
    rw [e0]
    have : (val st.qhat - 1) * val (v.take s) = val st.qhat * val (v.take s) - val (v.take s) := by
      rw [Nat.sub_mul, Nat.one_mul]
    omega
  · simp only [corrOnce]; rw [hvw', hwv]; rw [Nat.add_mul, Nat.one_mul]; omega
  · simp only [corrOnce]; omega
  · right
    simp only [corrOnce]
    have hge : 2 ^ (64 * (n - 1)) ≤ val (upd st.w s (addTo (st.w.drop s) (v.drop s))) := by
      rw [hvw']
      have : 2 ^ (64 * (n - 1)) ≤ 2 ^ 63 * 2 ^ (64 * (n - 1)) :=
        Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 63)
      omega
    have := lt_length_norm hww' hge
    omega


theorem cmpInt_pos_iff (a b : Nat) : 0 < cmpInt a b ↔ b < a := by
  unfold cmpInt
  split
  · constructor <;> intro h <;> omega
  · split <;> constructor <;> intro h <;> omega

theorem cmpQ_pos_iff {v n s B ql L} (c : Ctx v n s B ql L) (lq qh Y X Q k : Nat) (st : St)
    (hI : Inv v n s ql L lq qh Y k st) (hX : X = qh * v1S v s + Y) (hQ : Q = X / val v) :
    0 < cmpQ ql st ↔ Q < val st.qhat := by
  obtain ⟨hwq, hwb, hww, hlq, hbl, hwl, hk, hbv, hwv, hblt, hnorm⟩ := hI
  have hqn := c.hqln
  have hlen : (st.buf.take ql).length = ql := by simp; omega
  have hmod : val (st.buf.take ql) = val st.buf := by
    rw [(val_take_mod st.buf ql hwb).1, Nat.mod_eq_of_lt hblt]
  have hcmp : cmpQ ql st = cmpInt (val st.buf) (val st.w) := by
    unfold cmpQ
    rw [natCmp_stale _ _ (hwb.take _) (Wd_norm hww) (normed_norm _)
      (by rcases hnorm with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hlen]; exact h)), hmod, val_norm]
  rw [hcmp, cmpInt_pos_iff, hbv]
  have hv0 := c.v_split
  have hvp : 0 < val v := by
    have := c.v1S_ge
    have : 0 < 2 ^ 63 * 2 ^ (64 * (n - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hXk : X = val st.qhat * v1S v s + val st.w := by
    rw [hwv, hX, ← hk]; rw [Nat.add_mul]; omega
  rw [hQ]
  exact (cmp_iff X (val v) (v1S v s) (val (v.take s)) (val st.qhat) (val st.w) hvp (by omega) hXk).symm

theorem corr1_inv {v n s B ql L} (c : Ctx v n s B ql L) (lq qh Y X Q : Nat)
    (hX : X = qh * v1S v s + Y) (hXL : X < 2 ^ (64 * L)) (hQ : Q = X / val v) (hQle : Q ≤ qh) :
    ∀ (i k : Nat) (st : St), k ≤ qh - Q → Inv v n s ql L lq qh Y k st → qh - Q ≤ k + i →
      Inv v n s ql L lq qh Y (qh - Q) (corr1 v s ql i st)
  | 0, k, st, hk, hI, hi => by
    have : k = qh - Q := by omega
    subst this; exact hI
  | i + 1, k, st, hk, hI, hi => by
    unfold corr1
    have hpos := cmpQ_pos_iff c lq qh Y X Q k st hI hX hQ
    by_cases h : cmpQ ql st ≤ 0
    · rw [if_pos h]
      have h2 : ¬ (Q < val st.qhat) := fun h3 => by have := hpos.2 h3; omega
      have h3 : val st.qhat + k = qh := hI.2.2.2.2.2.2.1
      have : k = qh - Q := by omega
      subst this; exact hI
    · rw [if_neg h]
      have h2 : Q < val st.qhat := hpos.1 (by omega)
      have h3 : val st.qhat + k = qh := hI.2.2.2.2.2.2.1
      exact corr1_inv c lq qh Y X Q hX hXL hQ hQle i (k + 1) _ (by omega)
        (corrOnce_inv c lq qh Y X k st hI hX hXL (by omega)) (by omega)

end FvModexp.Mdl
