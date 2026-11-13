import FvModexp.Proofs.Arm64.Exp.OddDefs
import FvModexp.Proofs.Common.SqrCost

set_option autoImplicit false

/-!
# Closed `(*Int).exp` budget, part 2: the Montgomery windows (`ExpOdd.OBud` / `ExpOdd.OCost`) (divmc s33)

Crude uniform bounds for `Run.Closed.BudOK`: modulus `n ≤ 128` words, `x` of `xl ≤ 128` words, stack length `l ≤ 1024`.
Every window cost is a sum of `stackNatCost`/`makeCost`/`blockSize` terms at stack lengths `≤ 2^13` (bounded by
unfolding) and of copies of the division cost `costD` (12 in the budget, 6 in the charged cost); `costD` itself is five
`nat.div` budgets on dividends `≤ 2n + 1`, at stack lengths `≤ 8192`, hence `≤ 5 D` for any `costF` bounded by `D` there.
-/

open Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpBud

theorem bs_le (n : Nat) (h : n ≤ 128) : blockSize (8 * n) true ≤ 2072 := by
  have := blockSize_le (8 * n) true; omega

theorem bs2_le (n : Nat) (h : n ≤ 128) : blockSize (8 * (2 * n + 4)) true ≤ 4184 := by
  have := blockSize_le (8 * (2 * n + 4)) true; omega

theorem mk_le (n : Nat) (h : n ≤ 128) : makeCost (1 + 128 * n / 64 + 1) ≤ 4216 := by
  have := makeCost_le_makeB (1 + 128 * n / 64 + 1); unfold makeB allocCost at this; omega

/-- path MAXIMUM (expmc s42): split a budget `s + max a b` into its paths -/
theorem addmax {s a b T : Nat} (h1 : s + a ≤ T) (h2 : s + b ≤ T) : s + max a b ≤ T := by omega
/-- the same for the charged window cost `s0 + xnPre + …` -/
theorem costmax {s0 a b c d e f T : Nat} (h1 : s0 + a + c + d + e + f ≤ T) (h2 : s0 + b + c + d + e + f ≤ T) :
    s0 + max a b + c + d + e + f ≤ T := by omega

theorem w4bud_le {n xl cD l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW4.W4Bud n xl cD l ≤ 20000000 + 12 * cD := by
  have := bs_le n hn; have := bs2_le n hn; have := mk_le n hn
  unfold ExpW4.W4Bud
  simp only [W4Pro.xnPre]
  repeat' apply addmax
  all_goals (unfold W4Pro.xjBud W4Pro.xnBudA W4Pro.xnBudAC W4Pro.xjBudA W4Pro.xnBudAB W4Pro.xnBudAA stackNatCost allocCost; simp only [StackNat.rnd]; omega)

theorem w2bud_le {n xl cD l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW2.W2Bud n xl cD l ≤ 20000000 + 12 * cD := by
  have := bs_le n hn; have := bs2_le n hn; have := mk_le n hn
  unfold ExpW2.W2Bud
  simp only [W2Pro.xnPre]
  repeat' apply addmax
  all_goals (unfold W2Pro.xjBud W2Pro.xnBudA W2Pro.xnBudAC W2Pro.xjBudA W2Pro.xnBudAB W2Pro.xnBudAA stackNatCost allocCost; simp only [StackNat.rnd]; omega)

theorem w4cost_le {n xl cD l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW4.W4Cost n xl cD l ≤ 20000000 + 6 * cD := by
  have := bs_le n hn; have := bs2_le n hn; have := mk_le n hn
  have := makeCost_le_makeB n; unfold makeB allocCost at this
  unfold ExpW4.W4Cost
  simp only [W4Pro.xnPre]
  repeat' apply costmax
  all_goals (unfold W4Pro.xjBudA W4Pro.xnBudAB W4Pro.xnBudAA stackNatCost allocCost; simp only [StackNat.rnd]; omega)

theorem w2cost_le {n xl cD l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW2.W2Cost n xl cD l ≤ 20000000 + 6 * cD := by
  have := bs_le n hn; have := bs2_le n hn; have := mk_le n hn
  have := makeCost_le_makeB n; unfold makeB allocCost at this
  unfold ExpW2.W2Cost
  simp only [W2Pro.xnPre]
  repeat' apply costmax
  all_goals (unfold W2Pro.xjBudA W2Pro.xnBudAB W2Pro.xnBudAA stackNatCost allocCost; simp only [StackNat.rnd]; omega)

section
variable (costF : Nat → Nat → Nat → Nat) (D : Nat)
  (hF : ∀ ℓ ul vl, ℓ ≤ 8192 → ul ≤ 385 → vl ≤ 129 → costF ℓ ul vl ≤ D)
include hF

theorem div4_le {n xl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW4.divCost costF n xl l ≤ 5 * D := by
  unfold ExpW4.divCost
  have := hF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (2 * n + 1) n (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (2 * n + 1) n (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (23 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (23 * n) + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  omega

theorem div2_le {n xl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpW2.divCost costF n xl l ≤ 5 * D := by
  unfold ExpW2.divCost
  have := hF (l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (2 * n + 1) n (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (2 * n + 1) n (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (11 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  have := hF (l + StackNat.rnd (11 * n) + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n
    (by simp only [StackNat.rnd]; omega) (by omega) (by omega)
  omega

/-- **the windows' budget** (`ExpOdd.OBud`) -/
theorem oBud_le {n xl yl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpOdd.OBud costF n xl yl l ≤ 20000000 + 60 * D := by
  unfold ExpOdd.OBud
  split
  · have := w4bud_le (cD := ExpW4.divCost costF n xl l) hn hx hl
    have := div4_le costF D hF hn hx hl; omega
  · have := w2bud_le (cD := ExpW2.divCost costF n xl l) hn hx hl
    have := div2_le costF D hF hn hx hl; omega

/-- **the windows' charged cost** (`ExpOdd.OCost`) -/
theorem oCost_le {n xl yl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpOdd.OCost costF n xl yl l ≤ 20000000 + 30 * D := by
  unfold ExpOdd.OCost
  split
  · have := w4cost_le (cD := ExpW4.divCost costF n xl l) hn hx hl
    have := div4_le costF D hF hn hx hl; omega
  · have := w2cost_le (cD := ExpW2.divCost costF n xl l) hn hx hl
    have := div2_le costF D hF hn hx hl; omega

end

end FvModexp.Arm64.ExpBud
