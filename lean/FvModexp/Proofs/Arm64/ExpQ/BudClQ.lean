import FvModexp.Proofs.Arm64.ExpQ.IExpClQ
import FvModexp.Proofs.Arm64.ExpQ.BudSlowQ
import FvModexp.Proofs.Arm64.ExpQ.BudWinQ

set_option autoImplicit false

/-!
# TIGHT COSTS: `IExp.BudClQ` from the per-term targets (agent expmc s44)

`budClQ_of`: the closed `(*Int).exp` budget bound `IExp.BudClQ` (PATH-MAX text, NOTES-conventions "[expmc s44]
ANNOUNCE") from the per-term targets of divmc's `BudQ.Targets` (`W = BudQ.opC (max xl n)`): expmc's own
`slow` (BudSlowQ), `obud`/`ocost` (BudWinQ) are PROVED here; the premises are the other owners' fields
`rem` (asm/divmc: `clRQ 0 xl n ≤ 4 W`), `even` (infra: `clEQ 0 xl yl n ≤ 72 W + yl·320 W`) and `p2` (infra:
`clP 0 xl yl lm ≤ 6 W + yl·64 W`). The release allowance is the factor-free `BudQ.ExpBudgetF`
(`ExpBudgetF ≤ RunIface.ExpBudget`: `bF_le`, so the bound holds with and without the temporary slack).
-/

namespace FvModexp.Arm64.IExp

/-- the factor-free allowance is below `RunIface.ExpBudget` (equal at `w = w'`; TIGHT COSTS final step, top s40) -/
theorem bF_le {w w' yl : Nat} (h : w ≤ w') (h1 : 1 ≤ w') :
    (8 * (64 * yl) + 128) * BudQ.opC w ≤ RunIface.ExpBudget w' yl := by
  unfold RunIface.ExpBudget
  have e1 : BudQ.opC w ≤ RunIface.opCost w' := by unfold BudQ.opC RunIface.opCost allocCost; omega
  exact Nat.mul_le_mul_left _ e1

/-- **`BudClQ` from the other owners' targets** (expmc's slow/obud/ocost proved) -/
theorem budClQ_of
    (hrem : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → clRQ 0 xl n ≤ 4 * BudQ.opC (max xl n))
    (heven : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
      clEQ 0 xl yl n ≤ 72 * BudQ.opC (max xl n) + yl * (320 * BudQ.opC (max xl n)))
    (hp2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      clP 0 xl yl lm ≤ 6 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n))) : BudClQ := by
  intro xl yl n lm hx hy hn0 hn hlm
  have hR := hrem xl n hx hn0 hn
  have hE := heven xl yl n hx hy hn0 hn
  have hP := hp2 xl yl n lm hx hy hn0 hn hlm
  have hS := Q.ExpSlow.slow_target (yl := yl) hx hn0 hn
  have hO := Q.BudW.obud_target (yl := yl) hx hn0 hn
  have hC := Q.BudW.ocost_target (yl := yl) hx hn0 hn
  have hB := bF_le (w := max xl n) (w' := max (max xl yl) n) (yl := yl) (by omega) (by omega)
  have m1 : makeCost 1 = 40 := by decide
  have mn := BudQ.makeCost_le16 n; have mx := BudQ.makeCost_le16 xl
  have hW := Q.BudW.opC_eq (max xl n)
  simp only [ExpN.NCost, ExpN.maxC, clSQ, clFQ] at hS ⊢
  generalize BudQ.opC (max xl n) = W at hR hE hP hS hO hC hB hW
  have e1 : yl * (128 * W) = 128 * (yl * W) := Nat.mul_left_comm _ _ _
  have e2 : yl * (320 * W) = 320 * (yl * W) := Nat.mul_left_comm _ _ _
  have e3 : yl * (64 * W) = 64 * (yl * W) := Nat.mul_left_comm _ _ _
  have e4 : (8 * (64 * yl) + 128) * W = 512 * (yl * W) + 128 * W := by
    rw [Nat.add_mul, show 8 * (64 * yl) = 512 * yl by omega, Nat.mul_assoc]
  rw [e1] at hS; rw [e2] at hE; rw [e3] at hP; rw [e4] at hB
  generalize yl * W = Y at hS hE hP hB
  constructor <;> omega

end FvModexp.Arm64.IExp
