import FvModexp.Proofs.Amd64.NatQ.DivMBase
import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.BudQ
import FvModexp.Proofs.Common.MulCostQB

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64): the Q-form `nat.div` budget fits `ModBudget` (divmc s61)

`Q.NatDiv.costMQ Q.drsCQ ul vl ≤ ModBudget (max ul vl)` for `ul, vl ≤ 128` — the cost bound `IMod.mod_ensD` takes for
top's closed `Q.NatDiv.ensMC`. `drsCQ` is bounded as in arm64's `Q.BudT.drsCQ_le` (Arm64/NatQ/BudRem.lean; amd64's
`Q.drsCQ` is a copy of the same definition): two recursion levels (divisor `< 40` → `0`) with the proved mul bounds
(Common/MulCostQB `mulCQ_le_B`): `≤ 138490` for `ul ≤ 129`, `n ≤ 128`; at `vl ≥ 40` the budget is `≥ 5.3 M`.
-/

namespace FvModexp.Amd64.Q.BudM

open FvModexp FvModexp.BudQ

private theorem mul_small {a b : Nat} (ha : a ≤ 33) (hb : b ≤ 31) : mulCQ a b ≤ 1112 := by
  have h := mulCQ_le_B (xl := a) (yl := b) (by omega)
  unfold mulCB at h; split at h <;> omega

private theorem mul_mid {a b : Nat} (ha : a ≤ 65) (hb : b ≤ 63) : mulCQ a b ≤ 22138 := by
  have h := mulCQ_le_B (xl := a) (yl := b) (by omega)
  unfold mulCB at h; split at h
  · omega
  · split at h <;> omega

private theorem steps_le {ul n : Nat} (hu : ul ≤ 129) (hn : ¬ n < 40) : (ul - n) / (n / 2) + 1 ≤ 5 := by
  have : (ul - n) / (n / 2) < 5 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  omega

theorem drsCQ_le1 {ul n : Nat} (hu : ul ≤ 129) (hn : n ≤ 65) : drsCQ ul n ≤ 5 * 1112 := by
  by_cases h40 : n < 40
  · rw [drsCQ_small h40]; exact Nat.zero_le _
  · rw [drsCQ_big h40, drsCQ_small (by omega), Nat.zero_add]
    exact Nat.mul_le_mul (steps_le hu h40) (mul_small (by omega) (by omega))

/-- `drsCQ ul n ≤ 138490` for `ul ≤ 129`, `n ≤ 128` -/
theorem drsCQ_le {ul n : Nat} (hu : ul ≤ 129) (hn : n ≤ 128) : drsCQ ul n ≤ 5 * (5 * 1112 + 22138) := by
  by_cases h40 : n < 40
  · rw [drsCQ_small h40]; exact Nat.zero_le _
  · rw [drsCQ_big h40]
    exact Nat.mul_le_mul (steps_le hu h40)
      (Nat.add_le_add (drsCQ_le1 hu (by omega)) (mul_mid (by omega) (by omega)))

/-- **`nat.div`'s Q-form budget (as `(*Int).QuoRem` calls it from `(*Int).Mod`, `stk == nil`) fits `ModBudget`** -/
theorem bud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 →
    Q.NatDiv.costMQ drsCQ ul vl ≤ RunIface.ModBudget (max ul vl) := by
  intro ul vl hu hv
  have hm1 := makeCost_le16 ul
  have hm2 := makeCost_le16 (ul + 1)
  have hm3 := makeCost_le16 (ul - vl + 1)
  have hm4 : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
  have hd : drsCQ (ul + 1) vl ≤ (if vl < 40 then 0 else 5 * (5 * 1112 + 22138)) := by
    split
    · rw [drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact drsCQ_le (by omega) hv
  have hw1 : ul ≤ max ul vl := Nat.le_max_left ul vl
  have hw2 : vl ≤ max ul vl := Nat.le_max_right ul vl
  simp only [Q.NatDiv.costMQ, Q.NatDiv.costQ, Q.DivLarge.costQ, Q.NatDiv.HM, stkRes, capB, potK,
    RunIface.ModBudget, RunIface.opCost, allocCost]
  split at hd <;> omega

end FvModexp.Amd64.Q.BudM
