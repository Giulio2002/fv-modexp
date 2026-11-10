import FvModexp.Proofs.Common.Karatsuba
/-!
# karatsubaSqr (natmul.go:257-332)

Analogue of `Karatsuba.lean` for squaring: `z1 = z0 + z2 - tx^2` with `tx = x0 - x1`; `z1.abs = sqr(tx.abs)` and `z1.neg = true`
(even if `z1.abs` is empty: a denormalised "-0", handled by `intAdd`).  `sqr` (`nat.sqr`) is the parameter `sqr` with `SqrContract`.
Storage facts as in `Karatsuba.lean`.
-/
namespace FvModexp.Mdl

/-- `SqrContract` restricted to operands shorter than `k` words. -/
def SqrContractLt (k : Nat) (sqr : List Nat → List Nat) : Prop :=
  ∀ a : List Nat, Wd a → a.length < k →
    Wd (sqr a) ∧ val (sqr a) = val a * val a ∧ Normed (sqr a) ∧ (sqr a).length ≤ 2 * a.length

def ksTx (x : List Nat) (n2 : Nat) : GInt := intSub ⟨false, norm (x.take n2)⟩ ⟨false, norm (x.drop n2)⟩
/-- `z1.abs = z1.abs.sqr(stk, tx.abs); z1.neg = true` (natmul.go:296-297). -/
def ksZ1m (sqr : List Nat → List Nat) (x : List Nat) (n2 : Nat) : GInt := ⟨true, sqr (ksTx x n2).abs⟩
def ksZ0 (sqr : List Nat → List Nat) (x : List Nat) (n2 : Nat) : List Nat := sqr (norm (x.take n2))
def ksZ2 (sqr : List Nat → List Nat) (x : List Nat) (n2 : Nat) : List Nat := sqr (norm (x.drop n2))
def ksZ1a (sqr : List Nat → List Nat) (x : List Nat) (n2 : Nat) : GInt :=
  intAdd (ksZ1m sqr x n2) ⟨false, ksZ0 sqr x n2⟩
def ksZ1b (sqr : List Nat → List Nat) (x : List Nat) (n2 : Nat) : GInt :=
  intAdd (ksZ1a sqr x n2) ⟨false, ksZ2 sqr x n2⟩

/-- natmul.go:257 `karatsubaSqr(stk, z, x)`: returns the final `z[0:2n]`.  The base case `basicSqr(stk, z, x)` gets zeros as the
(irrelevant) old contents of `z` (`basicSqr_spec` holds for any). -/
def karatsubaSqr (sqr : List Nat → List Nat) (x : List Nat) : List Nat :=
  let n := x.length
  if n < karatsubaSqrThreshold ∨ n < 2 then basicSqr (List.replicate (2 * n) 0) x else
  let n2 := kN2 n
  let zz := kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)
  zz.take n2 ++ addTo (zz.drop n2) (ksZ1b sqr x n2).abs

structure KSqrFacts (sqr : List Nat → List Nat) (x : List Nat) : Prop where
  tx_ok : (ksTx x (kN2 x.length)).Ok
  tx_len : (ksTx x (kN2 x.length)).abs.length ≤ kN2 x.length
  z1m_len : (ksZ1m sqr x (kN2 x.length)).abs.length ≤ 2 * kN2 x.length
  z0_len : (ksZ0 sqr x (kN2 x.length)).length ≤ 2 * kN2 x.length
  z2_len : (ksZ2 sqr x (kN2 x.length)).length ≤ 2 * (x.length - kN2 x.length)
  z1a_len : (ksZ1a sqr x (kN2 x.length)).abs.length ≤ 2 * kN2 x.length + 1
  z1b_neg : (ksZ1b sqr x (kN2 x.length)).neg = false
  z1b_val : val (ksZ1b sqr x (kN2 x.length)).abs = 2 * (val (x.take (kN2 x.length)) * val (x.drop (kN2 x.length)))
  z1b_len : (ksZ1b sqr x (kN2 x.length)).abs.length ≤ x.length + 1
  z1b_len2 : (ksZ1b sqr x (kN2 x.length)).abs.length ≤ 2 * x.length - kN2 x.length
  z1b_len3 : (ksZ1b sqr x (kN2 x.length)).abs.length ≤ 2 * kN2 x.length + 1
  z1b_ok : (ksZ1b sqr x (kN2 x.length)).Ok
  zz_wd : Wd (kZ x.length (kN2 x.length) (ksZ0 sqr x (kN2 x.length)) (ksZ2 sqr x (kN2 x.length)))
  zz_len : (kZ x.length (kN2 x.length) (ksZ0 sqr x (kN2 x.length)) (ksZ2 sqr x (kN2 x.length))).length = 2 * x.length
  total : val x * val x = val (kZ x.length (kN2 x.length) (ksZ0 sqr x (kN2 x.length)) (ksZ2 sqr x (kN2 x.length))) +
    2 ^ (64 * kN2 x.length) * val (ksZ1b sqr x (kN2 x.length)).abs
  addTo_no_overflow : val ((kZ x.length (kN2 x.length) (ksZ0 sqr x (kN2 x.length)) (ksZ2 sqr x (kN2 x.length))).drop (kN2 x.length)) +
    val (ksZ1b sqr x (kN2 x.length)).abs < 2 ^ (64 * (2 * x.length - kN2 x.length))

theorem karatsubaSqr_facts (sqr : List Nat → List Nat) (x : List Nat) (hs : SqrContractLt x.length sqr)
    (hx : Wd x) (hn : 80 ≤ x.length) : KSqrFacts sqr x := by
  generalize hnn : x.length = n at *
  have hn2 : kN2 n = (n + 1) / 2 := rfl
  generalize hk : kN2 n = n2 at *
  have hn2a : n2 ≤ n - 1 := by omega
  have hn2b : n ≤ 2 * n2 := by omega
  have hx0W := Wd_norm (hx.take n2)
  have hx1W := Wd_norm (hx.drop n2)
  have hx0N := normed_norm (x.take n2)
  have hx1N := normed_norm (x.drop n2)
  have hx0L : (norm (x.take n2)).length ≤ n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_take]; omega)
  have hx1L : (norm (x.drop n2)).length ≤ n - n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_drop]; omega)
  have hXs := val_split x n2 (by omega)
  have hX0 : val (x.take n2) < 2 ^ (64 * n2) := by
    have := val_lt (hx.take n2); rw [show (x.take n2).length = n2 by simp [List.length_take]; omega] at this; exact this
  have hX1 : val (x.drop n2) < 2 ^ (64 * (n - n2)) := by
    have := val_lt (hx.drop n2); rw [show (x.drop n2).length = n - n2 by simp [List.length_drop]; omega] at this; exact this
  have hQP : 2 ^ (64 * (n - n2)) ≤ 2 ^ (64 * n2) := Nat.pow_le_pow_right (by decide) (by omega)
  have ePn : 2 ^ (64 * n) = 2 ^ (64 * n2) * 2 ^ (64 * (n - n2)) := by rw [← Nat.pow_add]; congr 1; omega
  have eP2 : 2 ^ (64 * (2 * n2)) = 2 ^ (64 * n2) * 2 ^ (64 * n2) := by rw [← Nat.pow_add]; congr 1; omega
  have eP2' : 2 ^ (64 * (2 * n - n2)) * 2 ^ (64 * n2) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hB1 : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm]
  have hBB : 2 ≤ 2 ^ 64 := by decide
  obtain ⟨tx1, tx2, tx3⟩ := intSub_spec ⟨false, norm (x.take n2)⟩ ⟨false, norm (x.drop n2)⟩ ⟨hx0W, hx0N⟩ ⟨hx1W, hx1N⟩
  rw [ival_false, ival_false, val_norm, val_norm] at tx3
  change (ksTx x n2).Ok at tx1
  have tx3' : (ksTx x n2).ival = ((val (x.take n2) : Nat) : Int) - ((val (x.drop n2) : Nat) : Int) := tx3
  have txl : (ksTx x n2).abs.length ≤ n2 := by
    apply len_le_of_val_lt tx1.1 tx1.2
    apply val_lt_of_ival
    · rw [tx3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
    · rw [tx3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
  -- z1 = -(tx^2)
  obtain ⟨q1, q2, q3, q4⟩ := hs (ksTx x n2).abs tx1.1 (by omega)
  have m1 : (ksZ1m sqr x n2).Ok := ⟨q1, q3⟩
  have m4' : (ksZ1m sqr x n2).abs.length ≤ 2 * n2 := by change (sqr (ksTx x n2).abs).length ≤ _; omega
  have m3 : (ksZ1m sqr x n2).ival = -(((val (x.take n2) : Int) - (val (x.drop n2) : Int)) * ((val (x.take n2) : Int) - (val (x.drop n2) : Int))) := by
    have hh : (ksZ1m sqr x n2).ival = -((val (sqr (ksTx x n2).abs) : Nat) : Int) := by
      unfold ksZ1m GInt.ival; simp
    rw [hh, q2]
    have : ((val (ksTx x n2).abs : Nat) : Int) * ((val (ksTx x n2).abs : Nat) : Int) =
        ((val (x.take n2) : Nat) - (val (x.drop n2) : Nat) : Int) * ((val (x.take n2) : Nat) - (val (x.drop n2) : Nat) : Int) := by
      rw [← tx3']; unfold GInt.ival
      cases (ksTx x n2).neg <;> simp <;> grind
    push_cast; rw [this]
  obtain ⟨z01, z02, z03, z04⟩ := hs _ hx0W (by omega)
  obtain ⟨z21, z22, z23, z24⟩ := hs _ hx1W (by omega)
  rw [val_norm] at z02 z22
  change Wd (ksZ0 sqr x n2) at z01
  change val (ksZ0 sqr x n2) = val (x.take n2) * val (x.take n2) at z02
  change Normed (ksZ0 sqr x n2) at z03
  change (ksZ0 sqr x n2).length ≤ _ at z04
  change Wd (ksZ2 sqr x n2) at z21
  change val (ksZ2 sqr x n2) = val (x.drop n2) * val (x.drop n2) at z22
  change Normed (ksZ2 sqr x n2) at z23
  change (ksZ2 sqr x n2).length ≤ _ at z24
  have z0l : (ksZ0 sqr x n2).length ≤ 2 * n2 := by omega
  have z2l : (ksZ2 sqr x n2).length ≤ 2 * (n - n2) := by omega
  have z1lt : val (ksZ1m sqr x n2).abs < 2 ^ (64 * (2 * n2)) := Nat.lt_of_lt_of_le (val_lt m1.1) (Nat.pow_le_pow_right (by decide) (by omega))
  -- z1a
  obtain ⟨a1, a2, a3⟩ := intAdd_spec (ksZ1m sqr x n2) ⟨false, ksZ0 sqr x n2⟩ m1 ⟨z01, z03⟩
  rw [ival_false] at a3
  change (ksZ1a sqr x n2).Ok at a1
  change (ksZ1a sqr x n2).ival = (ksZ1m sqr x n2).ival + ((val (ksZ0 sqr x n2) : Nat) : Int) at a3
  have z0lt : val (ksZ0 sqr x n2) < 2 ^ (64 * (2 * n2)) := Nat.lt_of_lt_of_le (val_lt z01) (Nat.pow_le_pow_right (by decide) (by omega))
  have m1v : (ksZ1m sqr x n2).ival < ((2 ^ (64 * (2 * n2)) : Nat) : Int) ∧ -(((2 ^ (64 * (2 * n2)) : Nat) : Int)) < (ksZ1m sqr x n2).ival := by
    unfold GInt.ival
    generalize 2 ^ (64 * (2 * n2)) = P at *
    cases (ksZ1m sqr x n2).neg <;> simp <;> omega
  have z1al : (ksZ1a sqr x n2).abs.length ≤ 2 * n2 + 1 := by
    apply len_le_of_val_lt a1.1 a1.2
    have hB : 2 ^ (64 * (2 * n2 + 1)) = 2 ^ 64 * 2 ^ (64 * (2 * n2)) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm]
    rw [hB]
    apply val_lt_of_ival
    · rw [a3]; generalize 2 ^ (64 * (2 * n2)) = P at *; omega
    · rw [a3]; generalize 2 ^ (64 * (2 * n2)) = P at *; omega
  -- z1b
  obtain ⟨b1, b2, b3⟩ := intAdd_spec (ksZ1a sqr x n2) ⟨false, ksZ2 sqr x n2⟩ a1 ⟨z21, z23⟩
  rw [ival_false] at b3
  change (ksZ1b sqr x n2).Ok at b1
  change (ksZ1b sqr x n2).Canon at b2
  change (ksZ1b sqr x n2).ival = (ksZ1a sqr x n2).ival + ((val (ksZ2 sqr x n2) : Nat) : Int) at b3
  have hZ : (ksZ1b sqr x n2).ival = ((2 * (val (x.take n2) * val (x.drop n2)) : Nat) : Int) := by
    rw [b3, a3, m3, z02, z22]
    push_cast
    grind
  have hZnn : 0 ≤ (ksZ1b sqr x n2).ival := by rw [hZ]; omega
  obtain ⟨nf, nv⟩ := ival_nonneg_neg_false _ b1 b2 hZnn
  have hV : val (ksZ1b sqr x n2).abs = 2 * (val (x.take n2) * val (x.drop n2)) := by
    rw [hZ] at nv; omega
  have hXY0 : val (x.take n2) * val (x.drop n2) < 2 ^ (64 * n) := by
    rw [ePn]; exact Nat.mul_lt_mul'' hX0 hX1
  have z1bl : (ksZ1b sqr x n2).abs.length ≤ n + 1 := by
    apply len_le_of_val_lt b1.1 b1.2
    rw [hV, hB1]; generalize 2 ^ (64 * n) = P at *; omega
  have hz2n : n + 1 ≤ 2 * n - n2 := by omega
  have hzc0 : Wd (List.replicate (2 * n) 0) := Wd_replicate_zero _
  have hu1l : (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)).length = 2 * n :=
    (length_upd _ _ _ (by simp; omega)).trans (by simp)
  have hu1W : Wd (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)) := Wd_upd hzc0 z01
  have hz1 : val (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)) = val (ksZ0 sqr x n2) := by
    have := val_upd_zero (List.replicate (2 * n) 0) (ksZ0 sqr x n2) 0 (by simp; omega)
      (fun e he => List.eq_of_mem_replicate (List.mem_of_mem_drop (List.mem_of_mem_take he)))
    rw [this, val_replicate_zero]; simp
  have hzz : Wd (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)) := Wd_upd hu1W z21
  have hzzl : (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)).length = 2 * n :=
    (length_upd _ _ _ (by rw [hu1l]; omega)).trans hu1l
  have hdz : (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)).drop (2 * n2) = (List.replicate (2 * n) 0).drop (2 * n2) :=
    drop_upd_far _ _ _ _ (by simp; omega) (by omega)
  have hzzv : val (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)) =
      val (ksZ0 sqr x n2) + 2 ^ (64 * (2 * n2)) * val (ksZ2 sqr x n2) := by
    unfold kZ
    have := val_upd_zero (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)) (ksZ2 sqr x n2) (2 * n2)
      (by rw [hu1l]; omega) (fun e he => by
        have h1 : e ∈ (upd (List.replicate (2 * n) 0) 0 (ksZ0 sqr x n2)).drop (2 * n2) := List.mem_of_mem_take he
        rw [hdz] at h1
        exact List.eq_of_mem_replicate (List.mem_of_mem_drop h1))
    rw [this, hz1]
  have hxy : val x * val x = val (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)) + 2 ^ (64 * n2) * val (ksZ1b sqr x n2).abs := by
    rw [hzzv, hV, z02, z22, eP2]
    have : val x * val x = (val (x.take n2) + 2 ^ (64 * n2) * val (x.drop n2)) * (val (x.take n2) + 2 ^ (64 * n2) * val (x.drop n2)) := by
      rw [← hXs]
    rw [this]
    generalize 2 ^ (64 * n2) = P at *
    grind
  have l2 : (ksZ1b sqr x n2).abs.length ≤ 2 * n - n2 := by omega
  have l3 : (ksZ1b sqr x n2).abs.length ≤ 2 * n2 + 1 := by omega
  suffices hno : val ((kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)).drop n2) + val (ksZ1b sqr x n2).abs < 2 ^ (64 * (2 * n - n2)) by
    subst hk; subst hnn
    exact ⟨tx1, txl, m4', z0l, z2l, z1al, nf, hV, z1bl, l2, l3, b1, hzz, hzzl, hxy, hno⟩
  have hxylt : val x * val x < 2 ^ (64 * n) * 2 ^ (64 * n) := by
    have hxl : val x < 2 ^ (64 * n) := by have := val_lt hx; rw [hnn] at this; exact this
    exact Nat.mul_lt_mul'' hxl hxl
  have hzzs := val_split (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)) n2 (by omega)
  rw [← eP2'] at hxylt
  apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * n2))
  rw [hxy] at hxylt
  generalize 2 ^ (64 * n2) = P at *
  generalize 2 ^ (64 * (2 * n - n2)) = R at *
  generalize val (List.drop n2 (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2))) = D at *
  generalize val (List.take n2 (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2))) = T at *
  generalize val (ksZ1b sqr x n2).abs = V at *
  generalize val (kZ n n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2)) = Zv at *
  grind

theorem karatsubaSqr_spec (sqr : List Nat → List Nat) (x : List Nat) (hs : SqrContractLt x.length sqr) (hx : Wd x) :
    (karatsubaSqr sqr x).length = 2 * x.length ∧ Wd (karatsubaSqr sqr x) ∧ val (karatsubaSqr sqr x) = val x * val x := by
  unfold karatsubaSqr
  simp only []
  by_cases hb : x.length < karatsubaSqrThreshold ∨ x.length < 2
  · rw [if_pos hb]
    by_cases h12 : 12 ≤ x.length
    · exact basicSqr_spec _ x (Wd_replicate_zero _) hx h12 (by simp)
    · -- n < 12: basicSqr falls back to basicMul
      unfold basicSqr
      simp only []
      rw [if_pos (by omega)]
      obtain ⟨a, b, c⟩ := basicMul_spec x x hx hx
      exact ⟨by omega, b, c⟩
  · rw [if_neg hb]
    have hn : 80 ≤ x.length := by unfold karatsubaSqrThreshold at hb; omega
    obtain ⟨_, _, _, _, _, _, _, _, _, fl2, _, fok, fzw, fzl, ftot, fno⟩ := karatsubaSqr_facts sqr x hs hx hn
    generalize hn2 : kN2 x.length = n2 at *
    have hn2' : n2 = (x.length + 1) / 2 := by rw [← hn2]; rfl
    generalize hzz : kZ x.length n2 (ksZ0 sqr x n2) (ksZ2 sqr x n2) = zz at *
    generalize hz1 : ksZ1b sqr x n2 = z1 at *
    obtain ⟨a1, a2, a3⟩ := addTo_spec (zz.drop n2) z1.abs (fzw.drop n2) fok.1
      (by simp [List.length_drop, fzl]; omega) (by
        simp only [List.length_drop, fzl]; exact fno)
    have hsp := val_split zz n2 (by omega)
    have ht : (zz.take n2).length = n2 := by simp [List.length_take]; omega
    refine ⟨by simp [List.length_append, a1, List.length_take, List.length_drop]; omega, Wd_append.2 ⟨fzw.take _, a2⟩, ?_⟩
    rw [val_append, ht, a3, ftot, hsp]
    have := Nat.mul_add (2 ^ (64 * n2)) (val (zz.drop n2)) (val z1.abs)
    omega

end FvModexp.Mdl
