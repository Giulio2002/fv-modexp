import FvModexp.Proofs.Arm64.Exp.OddDefs
import FvModexp.Proofs.Arm64.ExpQ.Bridge
import FvModexp.Proofs.Arm64.ExpQ.DrsCQB
import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# TIGHT COSTS BudOK: `Targets.obud` / `Targets.ocost` for the Montgomery windows at the top (agent expmc s44)

`ExpOdd.OBud`/`OCost` at the bridged `nat.div` cost `Q.divBr (Q.NatDiv.costQ Q.drsCQ)` (= `IExp.clFQ`) and level `0`
are at most `16·W`, `W = BudQ.opC (max xl n)` (divmc's `BudQ.Targets.obud/ocost`; mirror worst 14.88 at `n = 1`).
`cf_le`: one bridged division `≤ 2592·ul + 16·(ul − n) + 160·ℓ + 11016 (+ 560·ul + 88·n + 1960 for n ≥ 40)` (DrsCQB);
`divCost` (the max of the window's five divisions) at the deepest level and the longest dividend; then each path of
`W4Bud`/`W2Bud`/`W4Cost`/`W2Cost` separately (`blockSize ≤ allocCost`, `makeCost k ≤ 16 k + 88`, `rnd` exact).
-/

open Janus Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.BudW

/-- the bound of one bridged division (`ul` dividend, `n` divisor, level `ℓ`) -/
@[reducible] def cfB (ℓ ul n : Nat) : Nat :=
  2592 * ul + 16 * (ul - n) + 160 * ℓ + 11016 + (if n < 40 then 0 else 560 * ul + 88 * n + 1960)

theorem cf_le {ℓ ul n : Nat} (hn : n ≤ 128) (hu : ul ≤ 384) : divBr (NatDiv.costQ drsCQ) ℓ ul n ≤ cfB ℓ ul n := by
  simp only [divBr, NatDiv.costQ, DivLarge.costQ, cfB]
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

/-! ## window-4 -/

theorem div4_le {n xl : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 ≤
      cfB (StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n))
        (max xl (2 * n + 1)) n := by
  unfold ExpW4.divCost
  simp only [Nat.zero_add]
  have t1 := cf_le (ℓ := StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) (ul := xl) hn (by omega)
  have t2 := cf_le (ℓ := StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t3 := cf_le (ℓ := StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (ul := 2 * n + 1) hn (by omega)
  have t4 := cf_le (ℓ := StackNat.rnd (23 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t5 := cf_le (ℓ := StackNat.rnd (23 * n) + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, ?_⟩⟩
  · exact Nat.le_trans t1 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t2 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t3 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t4 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t5 (cfB_mono (by omega) (by omega))


theorem amax {a b c r : Nat} (h1 : a + b ≤ r) (h2 : a + c ≤ r) : a + max b c ≤ r := by omega

theorem rnd_le (k : Nat) : k ≤ StackNat.rnd k ∧ StackNat.rnd k ≤ k + 3 := by simp only [StackNat.rnd]; omega

set_option maxHeartbeats 4000000 in
/-- **window-4's budget at the top** -/
theorem obud4 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW4.W4Bud n xl (ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0) 0 ≤ 16 * BudQ.opC (max xl n) := by
  have hD := div4_le hn hx
  generalize ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 = D at hD
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hM : max xl n ≤ 128 := by omega
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW4.W4Bud, W4Pro.xjBud, W4Pro.xnBudA, W4Pro.xnBudAC, W4Pro.xnPre, W4Pro.xjBudA, W4Pro.xnBudAB,
    W4Pro.xnBudAA, stackNatCost, allocCost, cfB, Nat.zero_add] at hD ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl n = M at hnM hxM hM ⊢
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    repeat' apply amax
    all_goals omega
  · rw [if_neg h40] at hDB
    repeat' apply amax
    all_goals omega

set_option maxHeartbeats 4000000 in
/-- **window-4's charged cost at the top** -/
theorem ocost4 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW4.W4Cost n xl (ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0) 0 ≤ 16 * BudQ.opC (max xl n) := by
  have hD := div4_le hn hx
  generalize ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 = D at hD
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hM : max xl n ≤ 128 := by omega
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW4.W4Cost, ExpW4.lvT, W4Pro.xjBud, W4Pro.xnBudA, W4Pro.xnBudAC, W4Pro.xnPre, W4Pro.xjBudA, W4Pro.xnBudAB,
    W4Pro.xnBudAA, stackNatCost, allocCost, cfB, Nat.zero_add] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  generalize makeCost n = K2 at mn ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl n = M at hnM hxM hM ⊢
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    omega
  · rw [if_neg h40] at hDB
    omega

/-! ## window-2 -/

theorem div2_le {n xl : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 ≤
      cfB (StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n))
        (max xl (2 * n + 1)) n := by
  unfold ExpW2.divCost
  simp only [Nat.zero_add]
  have t1 := cf_le (ℓ := StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) (ul := xl) hn (by omega)
  have t2 := cf_le (ℓ := StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t3 := cf_le (ℓ := StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (ul := 2 * n + 1) hn (by omega)
  have t4 := cf_le (ℓ := StackNat.rnd (11 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t5 := cf_le (ℓ := StackNat.rnd (11 * n) + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, ?_⟩⟩
  · exact Nat.le_trans t1 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t2 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t3 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t4 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t5 (cfB_mono (by omega) (by omega))




set_option maxHeartbeats 4000000 in
/-- **window-2's budget at the top** -/
theorem obud2 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW2.W2Bud n xl (ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0) 0 ≤ 16 * BudQ.opC (max xl n) := by
  have hD := div2_le hn hx
  generalize ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 = D at hD
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hM : max xl n ≤ 128 := by omega
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW2.W2Bud, W2Pro.xjBud, W2Pro.xnBudA, W2Pro.xnBudAC, W2Pro.xnPre, W2Pro.xjBudA, W2Pro.xnBudAB,
    W2Pro.xnBudAA, stackNatCost, allocCost, cfB, Nat.zero_add] at hD ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl n = M at hnM hxM hM ⊢
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    repeat' apply amax
    all_goals omega
  · rw [if_neg h40] at hDB
    repeat' apply amax
    all_goals omega

set_option maxHeartbeats 4000000 in
/-- **window-2's charged cost at the top** -/
theorem ocost2 {n xl : Nat} (hn0 : 0 < n) (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW2.W2Cost n xl (ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0) 0 ≤ 16 * BudQ.opC (max xl n) := by
  have hD := div2_le hn hx
  generalize ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl 0 = D at hD
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hM : max xl n ≤ 128 := by omega
  have hU : max xl (2 * n + 1) ≤ 2 * max xl n + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW2.W2Cost, ExpW2.lvT, W2Pro.xjBud, W2Pro.xnBudA, W2Pro.xnBudAC, W2Pro.xnPre, W2Pro.xjBudA, W2Pro.xnBudAB,
    W2Pro.xnBudAA, stackNatCost, allocCost, cfB, Nat.zero_add] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  generalize makeCost n = K2 at mn ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl n = M at hnM hxM hM ⊢
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    omega
  · rw [if_neg h40] at hDB
    omega

/-! ## the targets -/

/-- **`Targets.obud`** -/
theorem obud_target {xl yl n : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) :
    ExpOdd.OBud (divBr (NatDiv.costQ drsCQ)) n xl yl 0 ≤ 16 * BudQ.opC (max xl n) := by
  unfold ExpOdd.OBud; split
  · exact obud4 hn0 hn hx
  · exact obud2 hn0 hn hx

/-- **`Targets.ocost`** -/
theorem ocost_target {xl yl n : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) :
    ExpOdd.OCost (divBr (NatDiv.costQ drsCQ)) n xl yl 0 ≤ 16 * BudQ.opC (max xl n) := by
  unfold ExpOdd.OCost; split
  · exact ocost4 hn0 hn hx
  · exact ocost2 hn0 hn hx

end FvModexp.Arm64.Q.BudW
