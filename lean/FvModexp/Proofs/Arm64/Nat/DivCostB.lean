import FvModexp.Proofs.Arm64.Nat.DrsDefs
import FvModexp.Proofs.Arm64.Nat.DivDefs
import FvModexp.Proofs.Common.MulCostB2

set_option autoImplicit false

/-!
# Crude uniform bounds of the `nat.div` budget (`NatDiv.cost DivRec.drsC`) for the closed `(*Int).exp` budget (divmc s33)

Dividends of at most 385 words, divisors of at most 129, stack length `ℓ ≤ 8192` (`Run.Closed.BudOK`).
`drsC` (`divRecursiveStep`) recurses on `n - n/2 + 1` words: `≤ 129 → ≤ 66 → ≤ 39 < 40` (three cases); its loop runs
`(ul - n)/(n/2) + 1 ≤ 20` (resp. `≤ 9`) times; the `qhat · v` products are `MC_small` (`n/2 - 1 < 40`) resp. box 1.
-/

open FvModexp

namespace FvModexp.Arm64.DivRec

/-- `divRecursiveStep` on a divisor of `40 ≤ n ≤ 76` words: base-case recursion, schoolbook products -/
theorem drsC_mid {ℓ ul n : Nat} (hl : ℓ ≤ 8500) (hu : ul ≤ 386) (h40 : 40 ≤ n) (hn : n ≤ 76) :
    drsC ℓ ul n ≤ 12000000 := by
  rw [drsC_big (by omega), drsC_small (by omega)]
  have hq : (ul - n) / (n / 2) + 1 ≤ 20 := by
    have := Nat.div_le_div_left (a := ul - n) (c := 20) (b := n / 2) (by omega) (by omega); omega
  have hM : mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 2168 := by
    unfold mulC
    have := MC_small (max (n / 2 + 1) (n / 2 - 1) + min (n / 2 + 1) (n / 2 - 1))
      (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (max (n / 2 + 1) (n / 2 - 1)) (min (n / 2 + 1) (n / 2 - 1))
      (Nat.le_refl _) (by omega)
    have := makeB_mono (k := max (n / 2 + 1) (n / 2 - 1) + min (n / 2 + 1) (n / 2 - 1)) (k' := 130) (by omega)
    unfold makeB allocCost at *; omega
  have hX : stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (n - n / 2 + 1 + 1) +
      stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
      mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 570000 := by
    have s1 : stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (n - n / 2 + 1 + 1) ≤ 280000 := by
      unfold stackNatCost allocCost; simp only [StackNat.rnd]; omega
    have s2 : stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) ≤ 285000 := by
      unfold stackNatCost allocCost; simp only [StackNat.rnd]; omega
    omega
  have hQ := Nat.mul_le_mul hq hX
  have hS : stackNatCost ℓ (n / 2 + 1) ≤ 280000 := by unfold stackNatCost allocCost; omega
  omega

/-- `divRecursiveStep` on a divisor of `77 ≤ n ≤ 129` words: recursion into `drsC_mid`, box-1 products -/
theorem drsC_hi {ℓ ul n : Nat} (hl : ℓ ≤ 8400) (hu : ul ≤ 386) (h77 : 77 ≤ n) (hn : n ≤ 129) :
    drsC ℓ ul n ≤ 820000000 := by
  rw [drsC_big (by omega)]
  have hq : (ul - n) / (n / 2) + 1 ≤ 9 := by
    have := Nat.div_le_div_left (a := ul - n) (c := 38) (b := n / 2) (by omega) (by omega)
    have := Nat.div_le_div_right (c := 38) (show ul - n ≤ 309 by omega); omega
  have hD := drsC_mid (ℓ := ℓ + StackNat.rnd (n / 2 + 1)) (ul := ul) (n := n - n / 2 + 1)
    (by simp only [StackNat.rnd]; omega) hu (by omega) (by omega)
  have hM := MC_box1 (max (n / 2 + 1) (n / 2 - 1) + min (n / 2 + 1) (n / 2 - 1))
    (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (max (n / 2 + 1) (n / 2 - 1)) (min (n / 2 + 1) (n / 2 - 1))
    65 (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _) (by simp only [StackNat.rnd]; omega)
  have hX : drsC (ℓ + StackNat.rnd (n / 2 + 1)) ul (n - n / 2 + 1) +
      stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
      mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 91000000 := by
    have hM' : mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 78315120 := by
      unfold mulC; omega
    have hS3 : stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) ≤ 290000 := by
      unfold stackNatCost allocCost; simp only [StackNat.rnd]; omega
    omega
  have hQ := Nat.mul_le_mul hq hX
  have hS : stackNatCost ℓ (n / 2 + 1) ≤ 272000 := by unfold stackNatCost allocCost; omega
  omega

/-- **`divRecursiveStep`**, every divisor length `≤ 129` -/
theorem drsC_le {ℓ ul n : Nat} (hl : ℓ ≤ 8400) (hu : ul ≤ 386) (hn : n ≤ 129) : drsC ℓ ul n ≤ 820000000 := by
  by_cases h40 : n < 40
  · rw [drsC_small h40]; unfold stackNatCost allocCost; omega
  by_cases h77 : n ≤ 76
  · have := drsC_mid (ℓ := ℓ) (by omega) hu (by omega) h77; omega
  · exact drsC_hi hl hu (by omega) hn

end FvModexp.Arm64.DivRec

namespace FvModexp.Arm64.NatDiv

/-- **`nat.div`'s budget**: dividend `≤ 385`, divisor `≤ 129` words, stack length `≤ 8192` -/
theorem costF_le {ℓ ul vl : Nat} (hl : ℓ ≤ 8192) (hu : ul ≤ 385) (hv : vl ≤ 129) :
    cost DivRec.drsC ℓ ul vl ≤ 825000000 := by
  have hD := DivRec.drsC_le (ℓ := ℓ + StackNat.rnd vl) (ul := ul + 1) (n := vl) (by simp only [StackNat.rnd]; omega)
    (by omega) hv
  have hX : max (stackNatCost (ℓ + StackNat.rnd vl) (vl + 1)) (DivRec.drsC (ℓ + StackNat.rnd vl) (ul + 1) vl) ≤
      820000000 := Nat.max_le.2 ⟨by unfold stackNatCost allocCost; simp only [StackNat.rnd]; omega, hD⟩
  have h1 := makeCost_le_makeB ul
  have h2 := makeCost_le_makeB 1
  have h3 := makeCost_le_makeB (ul + 1)
  have h4 := makeCost_le_makeB (ul - vl + 1)
  unfold cost DivLarge.cost
  unfold makeB stackNatCost allocCost at *
  omega

end FvModexp.Arm64.NatDiv
