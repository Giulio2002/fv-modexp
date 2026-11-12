import FvModexp.Proofs.Arm64.Nat.DrsDefs
import FvModexp.Proofs.Arm64.Nat.DivMDefs
import FvModexp.Proofs.Common.MulCostB

set_option autoImplicit false

/-!
# `(*Int).Mod` (arm64): `nat.div`'s budget fits `ModBudget` (operands of at most 128 words)

`NatDiv.costM DivRec.drsC ul vl ≤ ModBudget (max ul vl)` for `ul, vl ≤ 128` (`bud`, the `hbud` premise of `IMod.ens`).
All terms but `divRecursiveStep`'s `drsC` are linear and small (`≤ 20 000`). `drsC ℓ (ul + 1) vl` (`ℓ = rnd vl`):
* `vl < 40`: `divBasic`'s `stk.nat(vl + 1)` only;
* `vl ≥ 40` (budget `≥ ModBudget 40 > 5.3 M`): two levels of `drsC_big` — at most `(129 - vl) / (vl / 2) + 1` wide digits
  (`≤ 5`; `≤ 2` for `vl ≥ 82`; `1` for `vl ≥ 87`), each a recursive call on `≤ 65` words (`drs2`: `≤ 130 000`, its own
  recursion is `divBasic`), `stk.nat(3 vl)` and `nat.mul` on `(vl/2 + 1, vl/2 - 1)` words (`MC_bnd`: `≤ 133 336 + J ·
  258 384` with `J = (2 (vl/2) - 79) / 2`, i.e. `0` below `vl = 82`, `≤ 3` below `vl = 87`, `≤ 24`).
Numeric mirror: scripts/gen/mod-budget-check.py (worst ratio 0.203).
-/

namespace FvModexp.Arm64.IMod

open FvModexp FvModexp.Arm64

theorem snc_eq (ℓ n : Nat) : stackNatCost ℓ n = 32 * ℓ + 32 * n + 184 := by
  unfold stackNatCost allocCost; omega

/-- `nat.mul(qhat, v[:B-1])` of a `divRecursiveStep` level with `B = h` -/
theorem mulC_q {ℓ h : Nat} (hh : h ≤ 64) (hl : ℓ ≤ 580) :
    mulC ℓ (h + 1) (h - 1) ≤ 133336 + 258384 * ((2 * h - 79) / 2) := by
  unfold mulC
  rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
  have hj : mulJ (h + 1) (h - 1) = (2 * h - 79) / 2 := by rw [mulJ_lt (by omega)]; omega
  have := MC_bnd (h + 1 + (h - 1)) ℓ (h + 1) (h - 1) (Nat.le_refl _) (by omega) (by omega) (by rw [hj]; omega)
  rw [hj] at this; exact this

/-- the inner level: `divRecursiveStep` on `n ≤ 65` words (its recursive call is `divBasic`) -/
theorem drs2 {ℓ U n : Nat} (hl : ℓ ≤ 196) (hU : U ≤ 129) (hn : n ≤ 65) : DivRec.drsC ℓ U n ≤ 130000 := by
  by_cases h40 : n < 40
  · rw [DivRec.drsC_small h40, snc_eq]; omega
  rw [DivRec.drsC_big h40]
  have hr1 : StackNat.rnd (n / 2 + 1) ≤ 36 := by simp only [StackNat.rnd]; omega
  have hX : DivRec.drsC (ℓ + StackNat.rnd (n / 2 + 1)) U (n - n / 2 + 1) +
      stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
      mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 23688 := by
    rw [DivRec.drsC_small (n := n - n / 2 + 1) (by omega), snc_eq, snc_eq]
    have hm : mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) ≤ 1112 := by
      unfold mulC
      rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
      have := MC_small _ (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1)
        (Nat.le_refl _) (by omega)
      have := makeB_mono (k := n / 2 + 1 + (n / 2 - 1)) (k' := 64) (by omega)
      unfold makeB allocCost at *; omega
    omega
  generalize DivRec.drsC (ℓ + StackNat.rnd (n / 2 + 1)) U (n - n / 2 + 1) +
      stackNatCost (ℓ + StackNat.rnd (n / 2 + 1)) (3 * n) +
      mulC (ℓ + StackNat.rnd (n / 2 + 1) + StackNat.rnd (3 * n)) (n / 2 + 1) (n / 2 - 1) = X at hX ⊢
  have hq : (U - n) / (n / 2) + 1 ≤ 5 := by
    have := (Nat.div_lt_iff_lt_mul (x := U - n) (y := 5) (k := n / 2) (by omega)).2 (by omega)
    omega
  have := Nat.mul_le_mul hq hX
  rw [snc_eq]; omega

/-- the top level: `divRecursiveStep(u, v)` with `len v = vl ∈ [40, 128]` at stack length `ℓ ≤ 128` -/
theorem drs1 {ℓ U vl : Nat} (hl : ℓ ≤ 128) (hU : U ≤ 129) (h40 : 40 ≤ vl) (hv : vl ≤ 128) :
    DivRec.drsC ℓ U vl + 20000 ≤ 131072 * vl + 132608 := by
  rw [DivRec.drsC_big (by omega)]
  have hr1 : StackNat.rnd (vl / 2 + 1) ≤ 68 := by simp only [StackNat.rnd]; omega
  have hr2 : StackNat.rnd (3 * vl) ≤ 384 := by simp only [StackNat.rnd]; omega
  have hX : DivRec.drsC (ℓ + StackNat.rnd (vl / 2 + 1)) U (vl - vl / 2 + 1) +
      stackNatCost (ℓ + StackNat.rnd (vl / 2 + 1)) (3 * vl) +
      mulC (ℓ + StackNat.rnd (vl / 2 + 1) + StackNat.rnd (3 * vl)) (vl / 2 + 1) (vl / 2 - 1) ≤
      282080 + 258384 * ((2 * (vl / 2) - 79) / 2) := by
    have hd := drs2 (ℓ := ℓ + StackNat.rnd (vl / 2 + 1)) (U := U) (n := vl - vl / 2 + 1) (by omega) hU (by omega)
    have hm := mulC_q (ℓ := ℓ + StackNat.rnd (vl / 2 + 1) + StackNat.rnd (3 * vl)) (h := vl / 2) (by omega)
      (by omega)
    rw [snc_eq]; omega
  generalize DivRec.drsC (ℓ + StackNat.rnd (vl / 2 + 1)) U (vl - vl / 2 + 1) +
      stackNatCost (ℓ + StackNat.rnd (vl / 2 + 1)) (3 * vl) +
      mulC (ℓ + StackNat.rnd (vl / 2 + 1) + StackNat.rnd (3 * vl)) (vl / 2 + 1) (vl / 2 - 1) = X at hX ⊢
  rw [snc_eq]
  by_cases h82 : vl < 82
  · have hq : (U - vl) / (vl / 2) + 1 ≤ 5 := by
      have := (Nat.div_lt_iff_lt_mul (x := U - vl) (y := 5) (k := vl / 2) (by omega)).2 (by omega)
      omega
    have := Nat.mul_le_mul hq hX
    omega
  by_cases h87 : vl < 87
  · have hq : (U - vl) / (vl / 2) + 1 ≤ 2 := by
      have := (Nat.div_lt_iff_lt_mul (x := U - vl) (y := 2) (k := vl / 2) (by omega)).2 (by omega)
      omega
    have := Nat.mul_le_mul hq hX
    omega
  · have hq : (U - vl) / (vl / 2) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hq, Nat.zero_add, Nat.one_mul]
    omega

/-- **`nat.div`'s budget (as `(*Int).QuoRem` calls it from `(*Int).Mod`) fits `ModBudget`** -/
theorem bud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 →
    NatDiv.costM DivRec.drsC ul vl ≤ RunIface.ModBudget (max ul vl) := by
  intro ul vl hu hv
  have hw1 : ul ≤ max ul vl := Nat.le_max_left ul vl
  have hw2 : vl ≤ max ul vl := Nat.le_max_right ul vl
  have hB : RunIface.ModBudget (max ul vl) = 131072 * max ul vl + 132608 := by
    unfold RunIface.ModBudget RunIface.opCost allocCost; omega
  rw [hB]
  simp only [NatDiv.costM, NatDiv.cost, DivLarge.cost, Nat.zero_add]
  have m1 := makeCost_le_makeB ul
  have m2 := makeCost_le_makeB 1
  have m3 := makeCost_le_makeB (ul + 1)
  have m4 := makeCost_le_makeB (ul - vl + 1)
  have hr : StackNat.rnd vl ≤ 128 := by simp only [StackNat.rnd]; omega
  unfold makeB allocCost at m1 m2 m3 m4
  rw [snc_eq, snc_eq]
  by_cases h40 : vl < 40
  · rw [DivRec.drsC_small h40, snc_eq, Nat.max_self]; omega
  · have hd := drs1 (ℓ := StackNat.rnd vl) (U := ul + 1) hr (by omega) (by omega) hv
    have hmx : max (32 * StackNat.rnd vl + 32 * (vl + 1) + 184) (DivRec.drsC (StackNat.rnd vl) (ul + 1) vl) ≤
        32 * StackNat.rnd vl + 32 * (vl + 1) + 184 + DivRec.drsC (StackNat.rnd vl) (ul + 1) vl :=
      Nat.max_le.2 ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
    omega

end FvModexp.Arm64.IMod
