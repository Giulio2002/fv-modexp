import FvModexp.Proofs.Amd64.Exp.OddDefs
import FvModexp.Proofs.Amd64.Exp.DivInst
import FvModexp.Proofs.Amd64.Exp.DrsCQB
import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# TIGHT COSTS (amd64): the Montgomery windows at the top of `nat.expNN` (agent expmc s83; twin of arm64 ExpQ/BudWinQ)

amd64's windows take ONE division bound `costD` (`XnB`: `costF ℓ ul n ≤ costD` at each of the x-normalisation's
division levels). At the top (`(*Int).exp` → `nat.expNN`, level `0`) it is chosen per operand size: `dW xl n` = the
closed bound `cfB` of one bridged division (`DivInst.divC`) at the DEEPEST level of those divisions and the longest
dividend `max xl (2n+1)` (`cf_le`: `≤ 2592·ul + 16·(ul−n) + 160·ℓ + 11016 (+ 560·ul + 88·n + 1960 for n ≥ 40)`).
Then `ExpOdd.OBud DivInst.divC n (dW xl n) xl yl 0 b` holds for every `b ≥ 32·W` (`obud`; the `x` normalisation
`XnB` needs `24·W`, the window frame `≤ 8·W`) and the charged cost
`ExpOdd.OCost n xl yl (dW xl n) 0 ≤ 32·W` (`ocost`), `W = BudQ.opC (max xl n)` (arm64: 16·W with a per-division
costD; amd64 charges the max division `dW` at each of its divisions).
-/

open Janus Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.BudW

open FvModexp.Amd64.DivInst (divBr divC)

/-- the bound of one bridged division (`ul` dividend, `n` divisor, level `ℓ`) -/
@[reducible] def cfB (ℓ ul n : Nat) : Nat :=
  2592 * ul + 16 * (ul - n) + 160 * ℓ + 11016 + (if n < 40 then 0 else 560 * ul + 88 * n + 1960)

theorem cf_le {ℓ ul n : Nat} (hn : n ≤ 128) (hu : ul ≤ 384) : divC ℓ ul n ≤ cfB ℓ ul n := by
  simp only [divC, divBr, NatDiv.costQ, DivLarge.costQ, cfB]
  have m1 := BudQ.makeCost_le16 ul; have m2 := BudQ.makeCost_le16 (ul + 1); have m3 := BudQ.makeCost_le16 (ul - n + 1)
  have m4 : makeCost 1 = 40 := by decide
  have hr : stkRes (ℓ + 16 * ul + 64) = 160 * ℓ + 2560 * ul + 10680 := by unfold stkRes capB potK; omega
  rw [hr]
  by_cases h40 : n < 40
  · rw [drsCQ_small h40, if_pos h40]; omega
  · rw [if_neg h40]; have := drsCQ_le (U := ul + 1) (n := n) hn (by omega); omega

theorem cfB_mono {ℓ ℓ' ul ul' n : Nat} (h1 : ℓ ≤ ℓ') (h2 : ul ≤ ul') : cfB ℓ ul n ≤ cfB ℓ' ul' n := by
  simp only [cfB]; split <;> omega

theorem bs_le (x : Nat) : blockSize x true ≤ 2 * x + 24 := by
  have := blockSize_le_allocCost x true; unfold allocCost at this; omega

theorem opC_eq (w : Nat) : BudQ.opC w = 2048 * w + 2072 := by unfold BudQ.opC allocCost; omega

theorem rnd_le (k : Nat) : k ≤ StackNat.rnd k ∧ StackNat.rnd k ≤ k + 3 := by simp only [StackNat.rnd]; omega

/-- the deepest division level of the windows' `x` normalisation at the top (window-4's frame `rnd (23 n)`) -/
@[reducible] def lW (n xl : Nat) : Nat :=
  StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n)

/-- **the windows' division bound at the top** -/
def dW (xl n : Nat) : Nat := cfB (lW n xl) (max xl (2 * n + 1)) n

theorem cfB_le (ℓ ul n : Nat) : cfB ℓ ul n ≤ 2592 * ul + 16 * (ul - n) + 160 * ℓ + 11016 + (560 * ul + 88 * n + 1960) := by
  simp only [cfB]; split <;> omega

theorem dW_le (xl n : Nat) : dW xl n ≤ 2592 * max xl (2 * n + 1) + 16 * (max xl (2 * n + 1) - n) + 160 * lW n xl +
    11016 + (560 * max xl (2 * n + 1) + 88 * n + 1960) := cfB_le _ _ _

/-- every division of the `x` normalisation (base level `a ≤ rnd (23 n)`) is within `dW` -/
theorem cf_dW {n xl a ℓ ul : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (ha : a ≤ StackNat.rnd (23 * n))
    (hℓ : ℓ ≤ a + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (hu : ul ≤ max xl (2 * n + 1)) : divC ℓ ul n ≤ dW xl n :=
  Nat.le_trans (cf_le hn (by omega)) (cfB_mono (by simp only [lW]; omega) hu)

theorem amax {a b c r : Nat} (h1 : a + b ≤ r) (h2 : a + c ≤ r) : a + max b c ≤ r := by omega

/-! ## window-4 -/

set_option maxHeartbeats 8000000 in
/-- the window-4 `x` normalisation's budget conditions at the top -/
theorem xnB4 {n xl b : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128)
    (hb : 24 * BudQ.opC (max xl n) ≤ b) :
    W4En.XnB divC n (dW xl n) (0 + StackNat.rnd (23 * n)) xl (b - stackNatCost 0 (23 * n)) := by
  rw [Nat.zero_add]
  have ha := Nat.le_refl (StackNat.rnd (23 * n))
  refine ⟨⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ?_, ?_,
    ?_, cf_dW hn hx ha (by omega) (by omega), ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩,
    ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ?_, ?_⟩
  all_goals
    have hnM : n ≤ max xl n := Nat.le_max_right _ _
    have hxM : xl ≤ max xl n := Nat.le_max_left _ _
    rw [opC_eq] at hb
    have hD := dW_le xl n
    simp only [W4Pro.xjBud, stackNatCost, allocCost, lW] at hD ⊢
    have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
    have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
    have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
    have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
    generalize dW xl n = D at hD ⊢
    generalize max xl (2 * n + 1) = U at hD hU
    generalize max xl n = M at hnM hxM hb hU
    generalize blockSize (8 * n) true = B1 at b1 ⊢
    generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
    generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
    generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
    generalize StackNat.rnd (xl - n + 1) = c1 at r2 hD ⊢
    generalize StackNat.rnd n = c at r3 hD ⊢
    generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
    omega

set_option maxHeartbeats 8000000 in
/-- the window-2 `x` normalisation's budget conditions at the top -/
theorem xnB2 {n xl b : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128)
    (hb : 24 * BudQ.opC (max xl n) ≤ b) :
    W2En.XnB divC n (dW xl n) (0 + StackNat.rnd (11 * n)) xl (b - stackNatCost 0 (11 * n)) := by
  rw [Nat.zero_add]
  have ha : StackNat.rnd (11 * n) ≤ StackNat.rnd (23 * n) := by simp only [StackNat.rnd]; omega
  refine ⟨⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ?_, ?_,
    ?_, cf_dW hn hx ha (by omega) (by omega), ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩,
    ⟨?_, ?_, ?_, cf_dW hn hx ha (by omega) (by omega)⟩, ?_, ?_⟩
  all_goals
    have hnM : n ≤ max xl n := Nat.le_max_right _ _
    have hxM : xl ≤ max xl n := Nat.le_max_left _ _
    rw [opC_eq] at hb
    have hD := dW_le xl n
    simp only [W2Pro.xjBud, stackNatCost, allocCost, lW] at hD ⊢
    have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
    have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
    have r1 := rnd_le (11 * n); have r1' := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
    have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
    generalize dW xl n = D at hD ⊢
    generalize max xl (2 * n + 1) = U at hD hU
    generalize max xl n = M at hnM hxM hb hU
    generalize blockSize (8 * n) true = B1 at b1 ⊢
    generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
    generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
    generalize StackNat.rnd (11 * n) = a at r1 ha ⊢
    generalize StackNat.rnd (23 * n) = a' at r1' hD ha
    generalize StackNat.rnd (xl - n + 1) = c1 at r2 hD ⊢
    generalize StackNat.rnd n = c at r3 hD ⊢
    generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
    omega

/-! ## the windows at the top -/

theorem snc_le {n M : Nat} (hn : n ≤ M) (k : Nat) (hk : k ≤ 23) : stackNatCost 0 (k * n) ≤ 8 * BudQ.opC M := by
  rw [opC_eq]; simp only [stackNatCost, allocCost]
  have : k * n ≤ 23 * M := Nat.mul_le_mul hk hn
  omega

/-- **the windows' budget at the top** (`ExpOdd.OBud` at `dW`, level `0`) -/
theorem obud {n xl yl b : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) (hb : 32 * BudQ.opC (max xl n) ≤ b) :
    ExpOdd.OBud divC n (dW xl n) xl yl 0 b := by
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  unfold ExpOdd.OBud
  split
  · have h := snc_le hnM 23 (by omega)
    exact ⟨xnB4 hn0 hn hx (by omega), by omega⟩
  · have h := snc_le hnM 11 (by omega)
    exact ⟨xnB2 hn0 hn hx (by omega), by omega⟩

set_option maxHeartbeats 8000000 in
/-- **window-4's charged cost at the top** -/
theorem ocost4 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    W4Pro.W4Cost n xl (dW xl n) 0 ≤ 32 * BudQ.opC (max xl n) := by
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hD := dW_le xl n
  rw [opC_eq]
  simp only [W4Pro.W4Cost, W4Pro.xnPreM, W4Pro.xjPre, W4Pro.lvT, W4Pro.lvU, stackNatCost, allocCost, lW,
    Nat.zero_add] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  generalize dW xl n = D at hD ⊢
  generalize max xl (2 * n + 1) = U at hD hU
  generalize max xl n = M at hnM hxM hU ⊢
  generalize makeCost n = K2 at mn ⊢
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = c1 at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  omega

set_option maxHeartbeats 8000000 in
/-- **window-2's charged cost at the top** -/
theorem ocost2 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    W2Pro.W2Cost n xl (dW xl n) 0 ≤ 32 * BudQ.opC (max xl n) := by
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hD := dW_le xl n
  rw [opC_eq]
  simp only [W2Pro.W2Cost, W2Pro.xnPreM, W2Pro.xjPre, W2Pro.lvT, W2Pro.lvU, stackNatCost, allocCost, lW,
    Nat.zero_add] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r1' := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  generalize dW xl n = D at hD ⊢
  generalize max xl (2 * n + 1) = U at hD hU
  generalize max xl n = M at hnM hxM hU ⊢
  generalize makeCost n = K2 at mn ⊢
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 ⊢
  generalize StackNat.rnd (23 * n) = a' at r1' hD
  generalize StackNat.rnd (xl - n + 1) = c1 at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  omega

/-- **the windows' charged cost at the top** (`ExpOdd.OCost` at `dW`, level `0`) -/
theorem ocost {n xl yl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpOdd.OCost n xl yl (dW xl n) 0 ≤ 32 * BudQ.opC (max xl n) := by
  unfold ExpOdd.OCost
  split
  · exact ocost4 hn0 hn hx
  · exact ocost2 hn0 hn hx

end FvModexp.Amd64.Q.BudW
