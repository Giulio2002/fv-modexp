import FvModexp.Proofs.Common.DivRecMid
/-!
# One recursive call + refinement (the common core of both blocks of `divRecursiveStep`, natdiv.go:777-834 / 853-889)

`RecOk rec N`: the recursive callee `qhat.divRecursiveStep(stk, uu[s:B+n], v[s:], depth+1)` is modelled by a function `rec` (z, u, v) ↦
(z', u'), required to satisfy the value contract of a step on divisors of length ≤ N: `z` cleared (all zero), `2·u < β^(n+len z)`.
-/
namespace FvModexp.Mdl

/-- Contract of the recursive step callee on divisors with at most `N` limbs. -/
def RecOk (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) : Prop :=
  ∀ z u v : List Nat, (∀ d ∈ z, d = 0) → Wd z → Wd u → Wd v → 2 ≤ v.length → 2 ^ 63 ≤ topLimb v → v.length ≤ N →
    2 * val u < 2 ^ (64 * (v.length + z.length)) →
    (rec z u v).1.length = z.length ∧ (rec z u v).2.length = u.length ∧ Wd (rec z u v).1 ∧ Wd (rec z u v).2 ∧
    val (rec z u v).1 = val u / val v ∧ val (rec z u v).2 = val u % val v ∧
    (∀ d ∈ (rec z u v).2.drop v.length, d = 0)

theorem v1_pos {v : List Nat} {n s : Nat} (hvn : v.length = n) (hs : s < n) (htop : 2 ^ 63 ≤ topLimb v) :
    0 < val (v.drop s) := by
  have hne : v.drop s ≠ [] := by intro e; have := congrArg List.length e; simp at this; omega
  have h := val_ge_top hne (by rw [topLimb_drop v s (by omega)]; exact htop)
  have : 0 < 2 ^ 63 * 2 ^ (64 * ((v.drop s).length - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  omega

theorem step_core (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) (hrec : RecOk rec N)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul) (blk2 : Bool)
    (v : List Nat) (n s B : Nat) (w : List Nat) (la : Nat)
    (hv : Wd v) (hvn : v.length = n) (htop : 2 ^ 63 ≤ topLimb v) (hsB : s + 1 = B) (h2B : 2 * B ≤ n) (hnN : n - s ≤ N)
    (hw : Wd w) (hwn : n ≤ w.length) (hla : la ≤ n + 1) (hsla : s + la ≤ w.length)
    (htail : ∀ d ∈ w.drop (s + la), d = 0) (hXv : val w < val v * 2 ^ (64 * (B + 1))) :
    let r := rec (List.replicate (B + 1) 0) ((w.drop s).take la) (v.drop s)
    let m := refMid mul blk2 v n s (norm r.1) (upd w s r.2)
    r.1.length = B + 1 ∧ r.2.length = la ∧ Wd r.2 ∧ Wd r.1 ∧
    m.q.length ≤ B + 1 ∧ Wd m.q ∧ val m.q = val w / val v ∧ m.w.length = w.length ∧ Wd m.w ∧
    val m.w = val w % val v ∧ m.c = 0 ∧ m.e ≤ 0 ∧ (norm r.1).length + s ≤ 3 * n ∧
    (2 * val w < 2 ^ (64 * (B + n)) → m.q.length ≤ B) := by
  intro r m
  have hsn : s < n := by omega
  have hB1 : 1 ≤ B := by omega
  have hdl : (v.drop s).length = n - s := by simp [hvn]
  have hwd : (w.drop s).length = w.length - s := by simp
  have hargl : ((w.drop s).take la).length = la := by simp; omega
  have hargw : Wd ((w.drop s).take la) := (hw.drop s).take _
  -- split w
  have hdrop : w.drop s = (w.drop s).take la ++ w.drop (s + la) := by
    have := List.take_append_drop la (w.drop s)
    rw [List.drop_drop] at this
    exact this.symm
  have hz : val (w.drop (s + la)) = 0 := val_eq_zero_iff.2 htail
  have hvd : val (w.drop s) = val ((w.drop s).take la) := by
    conv => lhs; rw [hdrop]
    rw [val_append, hz]; simp
  have hwsplit := take_len_drop_val w s (by omega)
  have hx0 : val (w.take s) < 2 ^ (64 * s) := by
    have := val_lt (hw.take s); rwa [show (w.take s).length = s by simp; omega] at this
  have hargt : val ((w.drop s).take la) < 2 ^ (64 * (n + 1)) := by
    have := val_lt hargw
    rw [hargl] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  -- the recursive call
  have hv1 := v1_pos hvn hsn htop
  have hcall := hrec (List.replicate (B + 1) 0) ((w.drop s).take la) (v.drop s)
    (fun d hd => List.eq_of_mem_replicate hd) (Wd_replicate_zero _) hargw (hv.drop s) (by rw [hdl]; omega)
    (by rw [topLimb_drop v s (by omega)]; exact htop) (by rw [hdl]; exact hnN)
    (by
      rw [hdl, List.length_replicate]
      have e : 2 ^ (64 * (n - s + (B + 1))) = 2 ^ (64 * (n + 1)) * 2 ^ 64 := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e]
      have : 2 ^ 64 = 2 * 2 ^ 63 := two_pow_64_eq
      have h63 : 1 ≤ 2 ^ 63 := Nat.one_le_two_pow
      have : 2 * val ((w.drop s).take la) < 2 * 2 ^ (64 * (n + 1)) := by omega
      have : 2 * 2 ^ (64 * (n + 1)) ≤ 2 ^ (64 * (n + 1)) * 2 ^ 64 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ : r.1.length = (List.replicate (B + 1) 0).length ∧
      r.2.length = ((w.drop s).take la).length ∧ Wd r.1 ∧ Wd r.2 ∧
      val r.1 = val ((w.drop s).take la) / val (v.drop s) ∧ val r.2 = val ((w.drop s).take la) % val (v.drop s) ∧
      (∀ d ∈ r.2.drop (v.drop s).length, d = 0) := hcall
  rw [List.length_replicate] at k1
  rw [hargl] at k2
  -- qhat and w1
  have hq : Wd (norm r.1) := Wd_norm k3
  have hqn : Normed (norm r.1) := normed_norm _
  have hql : (norm r.1).length ≤ B + 1 := Nat.le_trans (length_norm_le _) (by omega)
  have hw1 : Wd (upd w s r.2) := Wd_upd hw k4
  have hw1l : (upd w s r.2).length = w.length := length_upd _ _ _ (by omega)
  have hu := val_upd w r.2 s (by omega)
  rw [k2] at hu
  -- values
  have hdm := Nat.div_add_mod (val ((w.drop s).take la)) (val (v.drop s))
  have hEQ : val (norm r.1) * v1S v s + val (upd w s r.2) = val w := by
    rw [val_norm, k5]
    unfold v1S
    rw [hvd] at hwsplit
    have k6' : val r.2 = val ((w.drop s).take la) % val (v.drop s) := k6
    generalize val ((w.drop s).take la) / val (v.drop s) = q at *
    generalize val ((w.drop s).take la) % val (v.drop s) = R2 at *
    generalize val ((w.drop s).take la) = A at *
    generalize val (v.drop s) = V1 at *
    generalize 2 ^ (64 * s) = S at *
    generalize val (upd w s r.2) = W1 at *
    generalize val r.2 = R at *
    have h3 : S * A = q * (V1 * S) + S * R2 := by rw [← hdm]; grind
    subst k6'
    omega
  have hspec := refMid_spec mul hmul blk2 v n s B w.length (norm r.1) (upd w s r.2) hv hvn htop hsB h2B hq hqn hql hw1 hw1l hwn
    (val ((w.drop s).take la) % val (v.drop s)) (val (w.take s)) (Nat.mod_lt _ hv1) hx0
    (by
      have h1 := hu; rw [k6] at h1
      have h2 := hwsplit; rw [hvd] at h2
      rw [Nat.mul_comm (val ((w.drop s).take la) % val (v.drop s))]
      omega)
    (by rw [hEQ]; exact val_lt hw) (by rw [hEQ]; exact hXv)
  rw [hEQ] at hspec
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hspec
  exact ⟨k1, k2, k4, k3, Nat.le_trans (Nat.le_of_eq s1) hql, s2, s3, s4, s5, s6, s7, s8, s9, fun h => Nat.le_trans (Nat.le_of_eq s1) (s10 h)⟩

end FvModexp.Mdl
