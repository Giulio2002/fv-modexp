import FvModexp.Proofs.Common.MulSqr
/-!
# karatsuba (natmul.go:164-250)

`karatsuba(stk, z, x, y)` with `len(x) = len(y) = n`, `len(z) = 2n`.  The recursive multiplications `z1.mul`, `z0.mul`, `z2.mul` go through
`nat.mul`, which is the parameter `mul` (contract `MulContract`); the closed recursive version is in `MulClosed.lean`.

Model of the storage (natmul.go:199-217):
* `tx := z[0:n2]`, `ty := z[n2:2n2]` are written by `Int.Sub`, read by `z1.mul`, and then dead (`clear(z)`).
  They fit because `|tx.abs|, |ty.abs| <= n2` (`karatsuba_facts.tx_len`, `.ty_len`): otherwise `nat.make` would run over `ty`'s storage.
* `clear(z)`, then `z0.mul(x0, y0)` stores the normalised product at `z[0:|z0|]` and `z2.mul(x1, y1)` at `z[2n2:2n2+|z2|]`
  (everything else stays 0): `kZ` below.
* `z1 += z0; z1 += z2` are `Int.Add` on `GInt`s with `neg = false` for `z0`, `z2`.
* `addTo(z[n2:], z1.abs)`.
-/
namespace FvModexp.Mdl

/-! ## small lemmas -/

theorem len_le_of_val_lt {l : List Nat} (hw : Wd l) (hn : Normed l) (m : Nat) (h : val l < 2 ^ (64 * m)) :
    l.length ≤ m := by
  by_cases hne : l = []
  · subst hne; simp
  · have h1 := hn.val_ge hne hw
    by_cases hc : l.length ≤ m
    · exact hc
    · have : 2 ^ (64 * m) ≤ 2 ^ (64 * (l.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega

theorem val_lt_of_ival (x : GInt) (M : Nat) (h1 : x.ival < M) (h2 : -(M : Int) < x.ival) : val x.abs < M := by
  unfold GInt.ival at h1 h2
  cases hh : x.neg <;> simp [hh] at h1 h2 <;> omega

theorem ival_nonneg_neg_false (x : GInt) (hx : x.Ok) (hc : x.Canon) (h : 0 ≤ x.ival) :
    x.neg = false ∧ x.ival = (val x.abs : Int) := by
  have : x.neg = false := by
    cases hn : x.neg
    · rfl
    · have := normed_val_pos hx.1 hx.2 (hc hn)
      unfold GInt.ival at h
      rw [hn] at h; simp only [if_true] at h; omega
  refine ⟨this, ?_⟩
  unfold GInt.ival; rw [this]; simp

/-- `MulContract` restricted to operands shorter than `k` words (what the recursion through `nat.mul` provides). -/
def MulContractLt (k : Nat) (mul : List Nat → List Nat → List Nat) : Prop :=
  ∀ a b : List Nat, Wd a → Wd b → a.length < k → b.length < k →
    Wd (mul a b) ∧ val (mul a b) = val a * val b ∧ Normed (mul a b) ∧ (mul a b).length ≤ a.length + b.length

/-! ## the model -/

/-- `n2 := (n + 1) / 2` (natmul.go:196). -/
def kN2 (n : Nat) : Nat := (n + 1) / 2

/-- `tx.Sub(x0, x1)` with `x0 = x[:n2].norm()`, `x1 = x[n2:].norm()`. -/
def kTx (x : List Nat) (n2 : Nat) : GInt := intSub ⟨false, norm (x.take n2)⟩ ⟨false, norm (x.drop n2)⟩
/-- `ty.Sub(y1, y0)`. -/
def kTy (y : List Nat) (n2 : Nat) : GInt := intSub ⟨false, norm (y.drop n2)⟩ ⟨false, norm (y.take n2)⟩
/-- `z1.mul(stk, tx, ty)` (`tx != ty` as pointers, so the sqr branch of `Int.mul` is not taken). -/
def kZ1m (mul : List Nat → List Nat → List Nat) (x y : List Nat) (n2 : Nat) : GInt :=
  intMul mul (fun _ => []) false (kTx x n2) (kTy y n2)
/-- `z0.mul(stk, x0, y0)` (abs of `z0`). -/
def kZ0 (mul : List Nat → List Nat → List Nat) (x y : List Nat) (n2 : Nat) : List Nat :=
  mul (norm (x.take n2)) (norm (y.take n2))
/-- `z2.mul(stk, x1, y1)` (abs of `z2`). -/
def kZ2 (mul : List Nat → List Nat → List Nat) (x y : List Nat) (n2 : Nat) : List Nat :=
  mul (norm (x.drop n2)) (norm (y.drop n2))
/-- `z1.Add(z1, z0)`. -/
def kZ1a (mul : List Nat → List Nat → List Nat) (x y : List Nat) (n2 : Nat) : GInt :=
  intAdd (kZ1m mul x y n2) ⟨false, kZ0 mul x y n2⟩
/-- `z1.Add(z1, z2)`. -/
def kZ1b (mul : List Nat → List Nat → List Nat) (x y : List Nat) (n2 : Nat) : GInt :=
  intAdd (kZ1a mul x y n2) ⟨false, kZ2 mul x y n2⟩
/-- `z` after `clear(z)`, `z0.mul`, `z2.mul` (products stored at `z[0:]` and `z[2n2:]`). -/
def kZ (n n2 : Nat) (z0 z2 : List Nat) : List Nat :=
  upd (upd (List.replicate (2 * n) 0) 0 z0) (2 * n2) z2

/-- natmul.go:164 `karatsuba(stk, z, x, y)`: returns the final `z[0:2n]`. -/
def karatsuba (mul : List Nat → List Nat → List Nat) (x y : List Nat) : List Nat :=
  let n := y.length
  if n < karatsubaThreshold ∨ n < 2 then basicMul x y else
  let n2 := kN2 n
  let zz := kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)
  zz.take n2 ++ addTo (zz.drop n2) (kZ1b mul x y n2).abs

/-! ## facts -/

/-- Everything the Go code relies on in the main branch (`n >= 40`). -/
structure KaraFacts (mul : List Nat → List Nat → List Nat) (x y : List Nat) : Prop where
  tx_ok : (kTx x (kN2 y.length)).Ok
  ty_ok : (kTy y (kN2 y.length)).Ok
  /-- `tx`, `ty` fit in `z[0:n2]`, `z[n2:2n2]`. -/
  tx_len : (kTx x (kN2 y.length)).abs.length ≤ kN2 y.length
  ty_len : (kTy y (kN2 y.length)).abs.length ≤ kN2 y.length
  /-- `z1.mul(tx, ty)` fits `stk.nat(2*n2+1)`. -/
  z1m_len : (kZ1m mul x y (kN2 y.length)).abs.length ≤ 2 * kN2 y.length
  z0_len : (kZ0 mul x y (kN2 y.length)).length ≤ 2 * kN2 y.length
  z2_len : (kZ2 mul x y (kN2 y.length)).length ≤ 2 * (y.length - kN2 y.length)
  z1a_len : (kZ1a mul x y (kN2 y.length)).abs.length ≤ 2 * kN2 y.length + 1
  /-- final `z1`: nonnegative, `= x0*y1 + x1*y0`, fits `stk.nat(2*n2+1)` and `z[n2:]` (the `addTo` slice bound). -/
  z1b_neg : (kZ1b mul x y (kN2 y.length)).neg = false
  z1b_val : val (kZ1b mul x y (kN2 y.length)).abs =
    val (x.take (kN2 y.length)) * val (y.drop (kN2 y.length)) + val (x.drop (kN2 y.length)) * val (y.take (kN2 y.length))
  z1b_len : (kZ1b mul x y (kN2 y.length)).abs.length ≤ y.length + 1
  z1b_len2 : (kZ1b mul x y (kN2 y.length)).abs.length ≤ 2 * y.length - kN2 y.length
  z1b_len3 : (kZ1b mul x y (kN2 y.length)).abs.length ≤ 2 * kN2 y.length + 1
  z1b_ok : (kZ1b mul x y (kN2 y.length)).Ok
  zz_wd : Wd (kZ y.length (kN2 y.length) (kZ0 mul x y (kN2 y.length)) (kZ2 mul x y (kN2 y.length)))
  zz_len : (kZ y.length (kN2 y.length) (kZ0 mul x y (kN2 y.length)) (kZ2 mul x y (kN2 y.length))).length = 2 * y.length
  /-- `x*y = z0 + B^{2 n2} z2 + B^{n2} z1` (the Karatsuba identity). -/
  total : val x * val y = val (kZ y.length (kN2 y.length) (kZ0 mul x y (kN2 y.length)) (kZ2 mul x y (kN2 y.length))) +
    2 ^ (64 * kN2 y.length) * val (kZ1b mul x y (kN2 y.length)).abs
  /-- `addTo(z[n2:], z1.abs)` drops no carry. -/
  addTo_no_overflow : val ((kZ y.length (kN2 y.length) (kZ0 mul x y (kN2 y.length)) (kZ2 mul x y (kN2 y.length))).drop (kN2 y.length)) +
    val (kZ1b mul x y (kN2 y.length)).abs < 2 ^ (64 * (2 * y.length - kN2 y.length))

theorem ival_false (l : List Nat) : (⟨false, l⟩ : GInt).ival = ((val l : Nat) : Int) := by simp [GInt.ival]

theorem karatsuba_facts (mul : List Nat → List Nat → List Nat) (x y : List Nat) (hm : MulContractLt y.length mul)
    (hx : Wd x) (hy : Wd y) (hl : x.length = y.length) (hn : 40 ≤ y.length) : KaraFacts mul x y := by
  generalize hnn : y.length = n at *
  have hn2 : kN2 n = (n + 1) / 2 := rfl
  generalize hk : kN2 n = n2 at *
  have hn2a : n2 ≤ n - 1 := by omega
  have hn2b : n ≤ 2 * n2 := by omega
  -- the four halves
  have hx0W := Wd_norm (hx.take n2)
  have hx1W := Wd_norm (hx.drop n2)
  have hy0W := Wd_norm (hy.take n2)
  have hy1W := Wd_norm (hy.drop n2)
  have hx0N := normed_norm (x.take n2)
  have hx1N := normed_norm (x.drop n2)
  have hy0N := normed_norm (y.take n2)
  have hy1N := normed_norm (y.drop n2)
  have hx0L : (norm (x.take n2)).length ≤ n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_take]; omega)
  have hy0L : (norm (y.take n2)).length ≤ n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_take]; omega)
  have hx1L : (norm (x.drop n2)).length ≤ n - n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_drop]; omega)
  have hy1L : (norm (y.drop n2)).length ≤ n - n2 := Nat.le_trans (length_norm_le _) (by simp [List.length_drop]; omega)
  -- values
  have hXs := val_split x n2 (by omega)
  have hYs := val_split y n2 (by omega)
  have hX0 : val (x.take n2) < 2 ^ (64 * n2) := by
    have := val_lt (hx.take n2); rw [show (x.take n2).length = n2 by simp [List.length_take]; omega] at this; exact this
  have hY0 : val (y.take n2) < 2 ^ (64 * n2) := by
    have := val_lt (hy.take n2); rw [show (y.take n2).length = n2 by simp [List.length_take]; omega] at this; exact this
  have hX1 : val (x.drop n2) < 2 ^ (64 * (n - n2)) := by
    have := val_lt (hx.drop n2); rw [show (x.drop n2).length = n - n2 by simp [List.length_drop]; omega] at this; exact this
  have hY1 : val (y.drop n2) < 2 ^ (64 * (n - n2)) := by
    have := val_lt (hy.drop n2); rw [show (y.drop n2).length = n - n2 by simp [List.length_drop]; omega] at this; exact this
  have hQP : 2 ^ (64 * (n - n2)) ≤ 2 ^ (64 * n2) := Nat.pow_le_pow_right (by decide) (by omega)
  have ePn : 2 ^ (64 * n) = 2 ^ (64 * n2) * 2 ^ (64 * (n - n2)) := by rw [← Nat.pow_add]; congr 1; omega
  have eP2 : 2 ^ (64 * (2 * n2)) = 2 ^ (64 * n2) * 2 ^ (64 * n2) := by rw [← Nat.pow_add]; congr 1; omega
  have eP2' : 2 ^ (64 * (2 * n - n2)) * 2 ^ (64 * n2) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hB1 : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm]
  have hBB : 2 ≤ 2 ^ 64 := by decide
  -- tx, ty
  obtain ⟨tx1, tx2, tx3⟩ := intSub_spec ⟨false, norm (x.take n2)⟩ ⟨false, norm (x.drop n2)⟩ ⟨hx0W, hx0N⟩ ⟨hx1W, hx1N⟩
  obtain ⟨ty1, ty2, ty3⟩ := intSub_spec ⟨false, norm (y.drop n2)⟩ ⟨false, norm (y.take n2)⟩ ⟨hy1W, hy1N⟩ ⟨hy0W, hy0N⟩
  rw [ival_false, ival_false, val_norm, val_norm] at tx3 ty3
  change (kTx x n2).Ok at tx1
  change (kTx x n2).Canon at tx2
  change (kTy y n2).Ok at ty1
  change (kTy y n2).Canon at ty2
  have tx3' : (kTx x n2).ival = ((val (x.take n2) : Nat) : Int) - ((val (x.drop n2) : Nat) : Int) := tx3
  have ty3' : (kTy y n2).ival = ((val (y.drop n2) : Nat) : Int) - ((val (y.take n2) : Nat) : Int) := ty3
  have txl : (kTx x n2).abs.length ≤ n2 := by
    apply len_le_of_val_lt tx1.1 tx1.2
    apply val_lt_of_ival
    · rw [tx3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
    · rw [tx3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
  have tyl : (kTy y n2).abs.length ≤ n2 := by
    apply len_le_of_val_lt ty1.1 ty1.2
    apply val_lt_of_ival
    · rw [ty3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
    · rw [ty3']; generalize 2 ^ (64 * n2) = P at *; generalize 2 ^ (64 * (n - n2)) = Q at *; omega
  -- z1 = tx * ty
  obtain ⟨m1, m2, m3, m4⟩ := intMul_ne_spec mul (fun _ => []) _ _ tx1 ty1 (fun w1 w2 => hm _ _ w1 w2 (by omega) (by omega))
  change (kZ1m mul x y n2).Ok at m1
  change (kZ1m mul x y n2).Canon at m2
  change (kZ1m mul x y n2).ival = (kTx x n2).ival * (kTy y n2).ival at m3
  change (kZ1m mul x y n2).abs.length ≤ (kTx x n2).abs.length + (kTy y n2).abs.length at m4
  have m4' : (kZ1m mul x y n2).abs.length ≤ 2 * n2 := by omega
  -- z0, z2
  obtain ⟨z01, z02, z03, z04⟩ := hm _ _ hx0W hy0W (by omega) (by omega)
  obtain ⟨z21, z22, z23, z24⟩ := hm _ _ hx1W hy1W (by omega) (by omega)
  rw [val_norm, val_norm] at z02 z22
  change Wd (kZ0 mul x y n2) at z01
  change val (kZ0 mul x y n2) = val (x.take n2) * val (y.take n2) at z02
  change Normed (kZ0 mul x y n2) at z03
  change (kZ0 mul x y n2).length ≤ _ at z04
  change Wd (kZ2 mul x y n2) at z21
  change val (kZ2 mul x y n2) = val (x.drop n2) * val (y.drop n2) at z22
  change Normed (kZ2 mul x y n2) at z23
  change (kZ2 mul x y n2).length ≤ _ at z24
  have z0l : (kZ0 mul x y n2).length ≤ 2 * n2 := by omega
  have z2l : (kZ2 mul x y n2).length ≤ 2 * (n - n2) := by omega
  have z0lt : val (kZ0 mul x y n2) < 2 ^ (64 * (2 * n2)) := Nat.lt_of_lt_of_le (val_lt z01) (Nat.pow_le_pow_right (by decide) (by omega))
  have z1lt : val (kZ1m mul x y n2).abs < 2 ^ (64 * (2 * n2)) := Nat.lt_of_lt_of_le (val_lt m1.1) (Nat.pow_le_pow_right (by decide) (by omega))
  have z2lt : val (kZ2 mul x y n2) < 2 ^ (64 * (2 * n2)) := Nat.lt_of_lt_of_le (val_lt z21) (Nat.pow_le_pow_right (by decide) (by omega))
  -- z1a
  obtain ⟨a1, a2, a3⟩ := intAdd_spec (kZ1m mul x y n2) ⟨false, kZ0 mul x y n2⟩ m1 ⟨z01, z03⟩
  rw [ival_false] at a3
  change (kZ1a mul x y n2).Ok at a1
  change (kZ1a mul x y n2).Canon at a2
  change (kZ1a mul x y n2).ival = (kZ1m mul x y n2).ival + ((val (kZ0 mul x y n2) : Nat) : Int) at a3
  have m1v : (kZ1m mul x y n2).ival < ((2 ^ (64 * (2 * n2)) : Nat) : Int) ∧ -(((2 ^ (64 * (2 * n2)) : Nat) : Int)) < (kZ1m mul x y n2).ival := by
    unfold GInt.ival
    generalize 2 ^ (64 * (2 * n2)) = P at *
    cases (kZ1m mul x y n2).neg <;> simp <;> omega
  have z1al : (kZ1a mul x y n2).abs.length ≤ 2 * n2 + 1 := by
    apply len_le_of_val_lt a1.1 a1.2
    have hB : 2 ^ (64 * (2 * n2 + 1)) = 2 ^ 64 * 2 ^ (64 * (2 * n2)) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm]
    rw [hB]
    apply val_lt_of_ival
    · rw [a3]; generalize 2 ^ (64 * (2 * n2)) = P at *; omega
    · rw [a3]; generalize 2 ^ (64 * (2 * n2)) = P at *; omega
  -- z1b
  obtain ⟨b1, b2, b3⟩ := intAdd_spec (kZ1a mul x y n2) ⟨false, kZ2 mul x y n2⟩ a1 ⟨z21, z23⟩
  rw [ival_false] at b3
  change (kZ1b mul x y n2).Ok at b1
  change (kZ1b mul x y n2).Canon at b2
  change (kZ1b mul x y n2).ival = (kZ1a mul x y n2).ival + ((val (kZ2 mul x y n2) : Nat) : Int) at b3
  have hZ : (kZ1b mul x y n2).ival = ((val (x.take n2) * val (y.drop n2) + val (x.drop n2) * val (y.take n2) : Nat) : Int) := by
    rw [b3, a3, m3, tx3', ty3', z02, z22]
    push_cast
    grind
  have hZnn : 0 ≤ (kZ1b mul x y n2).ival := by rw [hZ]; omega
  obtain ⟨nf, nv⟩ := ival_nonneg_neg_false _ b1 b2 hZnn
  have hV : val (kZ1b mul x y n2).abs = val (x.take n2) * val (y.drop n2) + val (x.drop n2) * val (y.take n2) := by
    rw [hZ] at nv; omega
  have hXY0 : val (x.take n2) * val (y.drop n2) < 2 ^ (64 * n) := by
    rw [ePn]; exact Nat.mul_lt_mul'' hX0 hY1
  have hXY1 : val (x.drop n2) * val (y.take n2) < 2 ^ (64 * n) := by
    rw [ePn]
    have := Nat.mul_lt_mul'' hY0 hX1
    rw [Nat.mul_comm (val (x.drop n2))]; exact this
  have z1bl : (kZ1b mul x y n2).abs.length ≤ n + 1 := by
    apply len_le_of_val_lt b1.1 b1.2
    rw [hV, hB1]; generalize 2 ^ (64 * n) = P at *; omega
  have hz2n : n + 1 ≤ 2 * n - n2 := by omega
  -- the stored z
  have hzc0 : Wd (List.replicate (2 * n) 0) := Wd_replicate_zero _
  have hu1l : (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)).length = 2 * n :=
    (length_upd _ _ _ (by simp; omega)).trans (by simp)
  have hu1W : Wd (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)) := Wd_upd hzc0 z01
  have hz1 : val (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)) = val (kZ0 mul x y n2) := by
    have := val_upd_zero (List.replicate (2 * n) 0) (kZ0 mul x y n2) 0 (by simp; omega)
      (fun e he => List.eq_of_mem_replicate (List.mem_of_mem_drop (List.mem_of_mem_take he)))
    rw [this, val_replicate_zero]; simp
  have hzz : Wd (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)) := Wd_upd hu1W z21
  have hzzl : (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)).length = 2 * n :=
    (length_upd _ _ _ (by rw [hu1l]; omega)).trans hu1l
  have hdz : (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)).drop (2 * n2) = (List.replicate (2 * n) 0).drop (2 * n2) :=
    drop_upd_far _ _ _ _ (by simp; omega) (by omega)
  have hzzv : val (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)) =
      val (kZ0 mul x y n2) + 2 ^ (64 * (2 * n2)) * val (kZ2 mul x y n2) := by
    unfold kZ
    have := val_upd_zero (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)) (kZ2 mul x y n2) (2 * n2)
      (by rw [hu1l]; omega) (fun e he => by
        have h1 : e ∈ (upd (List.replicate (2 * n) 0) 0 (kZ0 mul x y n2)).drop (2 * n2) := List.mem_of_mem_take he
        rw [hdz] at h1
        exact List.eq_of_mem_replicate (List.mem_of_mem_drop h1))
    rw [this, hz1]
  -- total value
  have hxy : val x * val y = val (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)) + 2 ^ (64 * n2) * val (kZ1b mul x y n2).abs := by
    rw [hzzv, hV, hXs, hYs, z02, z22]
    have e : 2 ^ (64 * (2 * n2)) = 2 ^ (64 * n2) * 2 ^ (64 * n2) := eP2
    rw [e]
    generalize 2 ^ (64 * n2) = P at *
    grind
  have l2 : (kZ1b mul x y n2).abs.length ≤ 2 * n - n2 := by omega
  have l3 : (kZ1b mul x y n2).abs.length ≤ 2 * n2 + 1 := by omega
  -- no overflow
  suffices hno : val ((kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)).drop n2) + val (kZ1b mul x y n2).abs < 2 ^ (64 * (2 * n - n2)) by
    subst hk; subst hnn
    exact ⟨tx1, ty1, txl, tyl, m4', z0l, z2l, z1al, nf, hV, z1bl, l2, l3, b1, hzz, hzzl, hxy, hno⟩
  have hxylt : val x * val y < 2 ^ (64 * n) * 2 ^ (64 * n) := by
    have hxl : val x < 2 ^ (64 * n) := by have := val_lt hx; rw [hl] at this; exact this
    have hyl : val y < 2 ^ (64 * n) := by have := val_lt hy; rw [hnn] at this; exact this
    exact Nat.mul_lt_mul'' hxl hyl
  have hzzs := val_split (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)) n2 (by omega)
  rw [← eP2'] at hxylt
  apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * n2))
  rw [hxy] at hxylt
  generalize 2 ^ (64 * n2) = P at *
  generalize 2 ^ (64 * (2 * n - n2)) = R at *
  generalize val (List.drop n2 (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2))) = D at *
  generalize val (List.take n2 (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2))) = T at *
  generalize val (kZ1b mul x y n2).abs = V at *
  generalize val (kZ n n2 (kZ0 mul x y n2) (kZ2 mul x y n2)) = Zv at *
  grind

theorem karatsuba_spec (mul : List Nat → List Nat → List Nat) (x y : List Nat) (hm : MulContractLt y.length mul)
    (hx : Wd x) (hy : Wd y) (hl : x.length = y.length) :
    (karatsuba mul x y).length = 2 * y.length ∧ Wd (karatsuba mul x y) ∧ val (karatsuba mul x y) = val x * val y := by
  unfold karatsuba
  simp only []
  by_cases hb : y.length < karatsubaThreshold ∨ y.length < 2
  · rw [if_pos hb]
    obtain ⟨a, b, c⟩ := basicMul_spec x y hx hy
    exact ⟨by omega, b, c⟩
  · rw [if_neg hb]
    have hn : 40 ≤ y.length := by unfold karatsubaThreshold at hb; omega
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, fl2, _, fok, fzw, fzl, ftot, fno⟩ := karatsuba_facts mul x y hm hx hy hl hn
    generalize hn2 : kN2 y.length = n2 at *
    have hn2' : n2 = (y.length + 1) / 2 := by rw [← hn2]; rfl
    generalize hzz : kZ y.length n2 (kZ0 mul x y n2) (kZ2 mul x y n2) = zz at *
    generalize hz1 : kZ1b mul x y n2 = z1 at *
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
