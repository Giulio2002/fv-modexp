import FvModexp.Proofs.Common.DivRecStep
/-!
# Spec of the common part of both blocks of `divRecursiveStep` (natdiv.go:797-834 / 853-889)

`refMid_spec`: given `qhat = ⌊x1/v1⌋` (normalised, from the recursive call) and `uu` already holding the remainder `r̂` in `uu[s:]`
(so `uu = r̂·β^s + x0`), the model computes the exact wide digit `⌊X/v⌋` (`X = qhat·v1·β^s + uu`) and the remainder `X mod v` in place,
with the two `panic("impossible")` tests unreachable and all slice bounds valid.
-/
namespace FvModexp.Mdl

theorem two_pow_64_eq : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by decide

theorem refMid_spec (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul) (blk2 : Bool)
    (v : List Nat) (n s B L : Nat) (qhat w : List Nat)
    (hv : Wd v) (hvn : v.length = n) (htop : 2 ^ 63 ≤ topLimb v) (hsB : s + 1 = B) (h2B : 2 * B ≤ n)
    (hq : Wd qhat) (hqn : Normed qhat) (hql : qhat.length ≤ B + 1)
    (hw : Wd w) (hwl : w.length = L) (hLn : n ≤ L)
    (r x0 : Nat) (hr : r < val (v.drop s)) (hx0 : x0 < 2 ^ (64 * s)) (hY : val w = r * 2 ^ (64 * s) + x0)
    (hXL : val qhat * v1S v s + val w < 2 ^ (64 * L))
    (hXv : val qhat * v1S v s + val w < val v * 2 ^ (64 * (B + 1))) :
    (refMid mul blk2 v n s qhat w).q.length = qhat.length ∧ Wd (refMid mul blk2 v n s qhat w).q ∧
    val (refMid mul blk2 v n s qhat w).q = (val qhat * v1S v s + val w) / val v ∧
    (refMid mul blk2 v n s qhat w).w.length = L ∧ Wd (refMid mul blk2 v n s qhat w).w ∧
    val (refMid mul blk2 v n s qhat w).w = (val qhat * v1S v s + val w) % val v ∧
    (refMid mul blk2 v n s qhat w).c = 0 ∧ (refMid mul blk2 v n s qhat w).e ≤ 0 ∧
    qhat.length + s ≤ 3 * n ∧ (2 * (val qhat * v1S v s + val w) < 2 ^ (64 * (B + n)) → qhat.length ≤ B) := by
  have hB1 : 1 ≤ B := by omega
  -- multiplication
  obtain ⟨p1, p2, p3, p4⟩ := hmul qhat (v.take s) hq (hv.take _)
  have hsn : s < n := by omega
  have hv0l : (v.take s).length = s := by simp [hvn]; omega
  have hp4 : (mul qhat (v.take s)).length ≤ B + 1 + s := by omega
  -- context
  have cx : Ctx v n s B (mul qhat (v.take s)).length L :=
    ⟨hv, hvn, htop, hsB, h2B, by omega, hLn⟩
  have hv0 := cx.v_split
  have hv1S := cx.v1S_ge
  have hMpos : 0 < 2 ^ 63 * 2 ^ (64 * (n - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hvp : 0 < val v := by omega
  generalize hXd : val qhat * v1S v s + val w = X at *
  generalize hqh : val qhat = qh at *
  generalize hQd : X / val v = Q
  have hX : X = qh * v1S v s + val w := hXd.symm
  -- good guess
  have hv1pos : 0 < val (v.drop s) := by
    rcases Nat.eq_zero_or_pos (val (v.drop s)) with h | h
    · exfalso; unfold v1S at hv1S; rw [h] at hv1S; simp at hv1S; omega
    · exact h
  have hx1 : X = (val (v.drop s) * qh + r) * 2 ^ (64 * s) + x0 := by
    rw [hX, hY]; unfold v1S
    rw [Nat.add_mul, Nat.mul_comm (val (v.drop s)) qh, Nat.mul_assoc]; omega
  have hvy : val v = val (v.drop s) * 2 ^ (64 * s) + val (v.take s) := by rw [hv0]; unfold v1S; omega
  have hqdiv : (val (v.drop s) * qh + r) / val (v.drop s) = qh := by
    rw [Nat.mul_add_div hv1pos, Nat.div_eq_of_lt hr]; simp
  have hlow : Q ≤ qh := by
    have := gg_lower X (val (v.drop s) * qh + r) x0 (val v) (val (v.drop s)) (val (v.take s)) (2 ^ (64 * s)) hx1 hx0 hvy hv1pos
    rw [hqdiv, hQd] at this; exact this
  have hT : 2 ^ (64 * (n - s)) ≤ 2 * val (v.drop s) := by
    have e1 : 2 ^ (64 * (n - s)) * 2 ^ (64 * s) = 2 * (2 ^ 63 * 2 ^ (64 * (n - 1))) := by
      rw [← Nat.pow_add, show 64 * (n - s) + 64 * s = 64 * (n - 1) + 64 by omega, Nat.pow_add, two_pow_64_eq]
      rw [Nat.mul_comm (2 ^ (64 * (n - 1))), Nat.mul_assoc]
    have : 2 ^ (64 * (n - s)) * 2 ^ (64 * s) ≤ (2 * val (v.drop s)) * 2 ^ (64 * s) := by
      unfold v1S at hv1S
      rw [e1, Nat.mul_assoc]; omega
    exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
  have hXT : X < val v * 2 ^ (64 * (n - s)) :=
    Nat.lt_of_lt_of_le hXv (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  have hy0 : val (v.take s) < 2 ^ (64 * s) := by
    have := val_lt (hv.take s); rwa [hv0l] at this
  have hup : qh ≤ Q + 2 := by
    have := gg_upper X (val (v.drop s) * qh + r) x0 (val v) (val (v.drop s)) (val (v.take s)) (2 ^ (64 * s)) (2 ^ (64 * (n - s)))
      hx1 hvy hy0 hT hXT hv1pos
    rw [hqdiv, hQd] at this; exact this
  -- length of qhat when the quotient is small
  have hsmall : 2 * X < 2 ^ (64 * (B + n)) → qhat.length ≤ B := by
    intro h2
    have hqlt : qh < 2 ^ (64 * B) := by
      refine Nat.lt_of_not_ge ?_
      intro hge
      have e : 2 ^ (64 * (B + n)) = 2 ^ (64 * B) * (2 * (2 ^ 63 * 2 ^ (64 * (n - 1)))) := by
        rw [Nat.mul_add, Nat.pow_add, show 64 * n = 64 * (n - 1) + 64 by omega, Nat.pow_add, two_pow_64_eq]
        ac_rfl
      have h3 : 2 ^ (64 * B) * (2 * (2 ^ 63 * 2 ^ (64 * (n - 1)))) ≤ qh * (2 * (2 ^ 63 * 2 ^ (64 * (n - 1)))) :=
        Nat.mul_le_mul_right _ hge
      have h4 : qh * (2 ^ 63 * 2 ^ (64 * (n - 1))) ≤ qh * v1S v s := Nat.mul_le_mul_left _ hv1S
      have h5 : qh * (2 * (2 ^ 63 * 2 ^ (64 * (n - 1)))) = 2 * (qh * (2 ^ 63 * 2 ^ (64 * (n - 1)))) := by
        rw [Nat.mul_left_comm]
      omega
    rw [← hqh] at hqlt
    exact length_le_of_normed hq hqn hqlt
  -- the initial state
  have hite : ∀ i st, (if blk2 then corr2 v s (mul qhat (v.take s)).length i else corr1 v s (mul qhat (v.take s)).length i) st
      = corr1 v s (mul qhat (v.take s)).length i st := by
    intro i st; cases blk2 <;> simp [corr2_eq_corr1]
  unfold refMid
  simp only []
  rw [hite]
  have hbuf : Wd (mul qhat (v.take s) ++ List.replicate (3 * n - (mul qhat (v.take s)).length) 0) :=
    Wd_append.2 ⟨p1, Wd_replicate_zero _⟩
  have hst0 : Inv v n s (mul qhat (v.take s)).length L qhat.length qh (val w) 0
      { qhat := qhat, buf := mul qhat (v.take s) ++ List.replicate (3 * n - (mul qhat (v.take s)).length) 0, w := w } := by
    refine ⟨hq, hbuf, hw, rfl, ?_, hwl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only []; rw [List.length_append, List.length_replicate]; omega
    · simp only []; omega
    · simp only []; rw [val_append_zeros, p2, ← hqh]
    · simp only []; omega
    · simp only []; rw [val_append_zeros]; have := val_lt p1; exact this
    · left; simp only []; rw [List.take_left]; exact p3
  have hfin := corr1_inv cx qhat.length qh (val w) X Q hX hXL hQd.symm hlow 2 0 _ (by omega) hst0 (by omega)
  generalize corr1 v s (mul qhat (v.take s)).length 2
      { qhat := qhat, buf := mul qhat (v.take s) ++ List.replicate (3 * n - (mul qhat (v.take s)).length) 0, w := w } = st at hfin ⊢
  have hfin' := hfin
  obtain ⟨hwq, hwb, hww, hlq, hbl, hwl2, hk, hbv, hwv, hblt, hnorm⟩ := hfin
  have hqQ : val st.qhat = Q := by omega
  have hqn3 := cx.hqln
  have hlen : (st.buf.take (mul qhat (v.take s)).length).length = (mul qhat (v.take s)).length := by simp; omega
  have hmod : val (st.buf.take (mul qhat (v.take s)).length) = val st.buf := by
    rw [(val_take_mod st.buf _ hwb).1, Nat.mod_eq_of_lt hblt]
  have hQv : Q * val v ≤ X := by rw [← hQd]; exact Nat.div_mul_le_self X (val v)
  have hqm : (qh - Q) * v1S v s = qh * v1S v s - Q * v1S v s := Nat.sub_mul _ _ _
  have hQm : Q * val v = Q * v1S v s + Q * val (v.take s) := by rw [hv0, Nat.mul_add, Nat.add_comm]
  have hQq : Q * v1S v s ≤ qh * v1S v s := Nat.mul_le_mul_right _ hlow
  have hle : val (st.buf.take (mul qhat (v.take s)).length) ≤ val st.w := by
    rw [hmod, hbv, hqQ, hwv]
    omega
  obtain ⟨d1, d2, d3, d4⟩ := subToC_spec st.w (st.buf.take (mul qhat (v.take s)).length) hww (hwb.take _) (by omega) hle
  have hdm := Nat.div_add_mod X (val v)
  refine ⟨hlq, hwq, hqQ, by rw [d1, hwl2], d2, ?_, d3, ?_, by omega, hsmall⟩
  · rw [hQd] at hdm
    rw [hmod, hbv, hqQ, hwv] at d4
    rw [Nat.mul_comm Q] at hQm hQv
    omega
  · have hnp := cmpQ_pos_iff cx qhat.length qh (val w) X Q (qh - Q) st hfin' hX hQd.symm
    refine Int.not_lt.1 (fun h => ?_)
    have := hnp.1 h
    omega

end FvModexp.Mdl
