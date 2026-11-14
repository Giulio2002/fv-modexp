import FvModexp.Proofs.Amd64.Exp.EvNP

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the `expNNOdd` window budget `ExpOdd.OBud` from a numeric bound (asm s65)

amd64 `ExpN.NPre` asks, besides the path-max budget `NBudE`, the closed budget `ExpOdd.OBud costF n costD xl yl l b`
of the called window (`W4En.XnB` / `W2En.XnB`): stack-level side conditions, division-cost side conditions
`costF … ≤ costD` and four budget sums. arm64 folded the latter into `NBudE`; here they are split off:
* `needO xl n`: the stack words above the call level that cover every level side condition (both windows);
* `ODem costD xl n l`: the numeric demand (the max of both windows' `stackNatCost l (23n | 11n)` + budget sums);
* **`obud_of`**: `l + needO xl n ≤ 2^16`, `costF ≤ costD` on levels `≤ l + needO xl n` (so `costD` may depend
  on the call level `l`: amd64 uses `EvCD.cD`, asm s73) and operand lengths `≤ 2n+1` or `≤ xl`,
  and `ODem costD xl n l ≤ b` give `OBud costF n costD xl ylen l b` (for every `ylen`);
* `NBudO = max NBudE (makeCost lm + ODem …)`: the Even body's budget premise (`bU` dominates it), and `obud_rk`
  turns `NBudO ≤ rk` into `segE1`/`segE2`'s `NBudE ≤ rk ∧ OBud … (rk - makeCost lm)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the stack words above the call level that `ExpOdd.OBud`'s level side conditions need (both windows) -/
@[reducible] def needO (xl n : Nat) : Nat :=
  StackNat.rnd (23 * n) + StackNat.rnd (xl + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n +
    16 * xl + 144

/-- the four budget sums of window-4's `XnB` at level `L` (their max) -/
@[reducible] def xnN4 (n costD L xl : Nat) : Nat :=
  max (max (W4Pro.xjBud n costD L) (stackNatCost L n + W4Pro.xjBud n costD (L + StackNat.rnd n)))
    (max (stackNatCost L (xl - n + 1) + (stackNatCost (L + StackNat.rnd (xl - n + 1)) n +
      (costD + W4Pro.xjBud n costD (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n))))
    (stackNatCost L (xl - n + 1) + (stackNatCost (L + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        W4Pro.xjBud n costD (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))))))

/-- the four budget sums of window-2's `XnB` at level `L` (their max) -/
@[reducible] def xnN2 (n costD L xl : Nat) : Nat :=
  max (max (W2Pro.xjBud n costD L) (stackNatCost L n + W2Pro.xjBud n costD (L + StackNat.rnd n)))
    (max (stackNatCost L (xl - n + 1) + (stackNatCost (L + StackNat.rnd (xl - n + 1)) n +
      (costD + W2Pro.xjBud n costD (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n))))
    (stackNatCost L (xl - n + 1) + (stackNatCost (L + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        W2Pro.xjBud n costD (L + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))))))

/-- the numeric demand of `ExpOdd.OBud` at level `l` (both windows) -/
@[reducible] def ODem (costD xl n l : Nat) : Nat :=
  max (stackNatCost l (23 * n) + xnN4 n costD (l + StackNat.rnd (23 * n)) xl)
    (stackNatCost l (11 * n) + xnN2 n costD (l + StackNat.rnd (11 * n)) xl)

/-- `NBudE` together with the window demand (the Even body's per-call budget) -/
@[reducible] def NBudO (costD : Nat) (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (xl yl lm l n : Nat) : Nat :=
  max (NBudE costR costS costP xl yl lm l n) (makeCost lm + ODem costD xl lm l)

theorem rndM {a b : Nat} (h : a ≤ b) : StackNat.rnd a ≤ StackNat.rnd b := by unfold StackNat.rnd; omega

section
variable {costF : Nat → Nat → Nat → Nat} {n costD xl B : Nat}

theorem xjl4_of {L : Nat} (hL : L + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hB : L + 2 * StackNat.rnd (2 * n) ≤ B)
    (hF : ∀ l' a, l' ≤ B → (a ≤ 2 * n + 1 ∨ a ≤ xl) → costF l' a n ≤ costD) : W4Pro.XjL costF n costD L :=
  ⟨by omega, by omega, by omega, hF _ _ hB (Or.inl (Nat.le_refl _))⟩

theorem xjl2_of {L : Nat} (hL : L + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hB : L + 2 * StackNat.rnd (2 * n) ≤ B)
    (hF : ∀ l' a, l' ≤ B → (a ≤ 2 * n + 1 ∨ a ≤ xl) → costF l' a n ≤ costD) : W2Pro.XjL costF n costD L :=
  ⟨by omega, by omega, by omega, hF _ _ hB (Or.inl (Nat.le_refl _))⟩

theorem xnb4_of {L b : Nat}
    (hL : L + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 16 * xl + 80 ≤
      2 ^ 16)
    (hB : L + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) ≤ B)
    (hF : ∀ l' a, l' ≤ B → (a ≤ 2 * n + 1 ∨ a ≤ xl) → costF l' a n ≤ costD) (hb : xnN4 n costD L xl ≤ b) :
    W4En.XnB costF n costD L xl b := by
  simp only [xnN4] at hb
  exact ⟨xjl4_of (by omega) (by omega) hF, xjl4_of (by omega) (by omega) hF, by omega, by omega, by omega,
    hF _ _ (by omega) (Or.inr (Nat.le_refl _)), xjl4_of (by omega) (by omega) hF, xjl4_of (by omega) (by omega) hF,
    by omega, by omega⟩

theorem xnb2_of {L b : Nat}
    (hL : L + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 16 * xl + 80 ≤
      2 ^ 16)
    (hB : L + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) ≤ B)
    (hF : ∀ l' a, l' ≤ B → (a ≤ 2 * n + 1 ∨ a ≤ xl) → costF l' a n ≤ costD) (hb : xnN2 n costD L xl ≤ b) :
    W2En.XnB costF n costD L xl b := by
  simp only [xnN2] at hb
  exact ⟨xjl2_of (by omega) (by omega) hF, xjl2_of (by omega) (by omega) hF, by omega, by omega, by omega,
    hF _ _ (by omega) (Or.inr (Nat.le_refl _)), xjl2_of (by omega) (by omega) hF, xjl2_of (by omega) (by omega) hF,
    by omega, by omega⟩

/-- **`ExpOdd.OBud` from the numeric demand** (see the module doc) -/
theorem obud_of {ylen l b : Nat} (hl : l + needO xl n ≤ 2 ^ 16)
    (hF : ∀ l' a, l' ≤ l + needO xl n → (a ≤ 2 * n + 1 ∨ a ≤ xl) → costF l' a n ≤ costD) (hb : ODem costD xl n l ≤ b) :
    ExpOdd.OBud costF n costD xl ylen l b := by
  have h1 := rndM (show xl - n + 1 ≤ xl + 1 by omega)
  have h2 := rndM (show 11 * n ≤ 23 * n by omega)
  have hB0 : l + StackNat.rnd (23 * n) + StackNat.rnd (xl + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n) ≤
      l + needO xl n := by simp only [needO]; omega
  simp only [ODem] at hb
  simp only [needO] at hl
  unfold ExpOdd.OBud
  split
  · exact ⟨xnb4_of (by omega) (by omega) hF (by omega), by omega⟩
  · exact ⟨xnb2_of (by omega) (by omega) hF (by omega), by omega⟩

end

/-- `segE1`/`segE2`'s per-call budget conjuncts from `NBudO ≤ rk` -/
theorem obud_rk {costF : Nat → Nat → Nat → Nat} {costD : Nat} {costR : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {xl yl lm l n rk : Nat}
    (h : NBudO costD costR costS costP xl yl lm l n ≤ rk) (hl : l + needO xl lm ≤ 2 ^ 16)
    (hF : ∀ l' a, l' ≤ l + needO xl lm → (a ≤ 2 * lm + 1 ∨ a ≤ xl) → costF l' a lm ≤ costD) :
    NBudE costR costS costP xl yl lm l n ≤ rk ∧ ExpOdd.OBud costF lm costD xl yl l (rk - makeCost lm) := by
  simp only [NBudO] at h
  exact ⟨by omega, obud_of hl hF (by omega)⟩

end FvModexp.Amd64.ExpEven
