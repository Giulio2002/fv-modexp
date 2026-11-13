import FvModexp.Proofs.Arm64.ExpQ.BudClQR
import FvModexp.Proofs.Arm64.ExpQ.BudP2Q

set_option autoImplicit false

/-!
# TIGHT COSTS: `IExp.BudClQ` with the P target at `8 W` and `hp2` discharged (divmc s42)

The Q-form `nat.expNNPowerOfTwo` (P2 chain converted, divmc s42) meets `clP 0 xl yl lm ≤ 8 W + yl·64 W`
(`Q.BudP2.hp2Q`; real mirror: setup ≤ 5.8 W — the closed op bounds give 6.35 W, so `6 W` is not provable with them).
`budClQ_of8`: expmc's `budClQ_of` with the P target `8 W` (same proof: the P branch sits under a path MAX with
`72 W`-sized branches); `budClQ_of_e`: `rem` (divmc's `Q.BudT.rem`) and `p2` plugged — only infra's `even` is open.
-/

namespace FvModexp.Arm64.IExp

/-- **`BudClQ` from the per-term targets, P at `8 W`** (copy of expmc's `budClQ_of`) -/
theorem budClQ_of8
    (hrem : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → clRQ 0 xl n ≤ 4 * BudQ.opC (max xl n))
    (heven : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
      clEQ 0 xl yl n ≤ 72 * BudQ.opC (max xl n) + yl * (320 * BudQ.opC (max xl n)))
    (hp2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      clP 0 xl yl lm ≤ 8 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n))) : BudClQ := by
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

/-- `hp2` for the Q-form `clP` (`= P2D.cP sqrCQ mulCQ`) -/
theorem hp2Cl : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    clP 0 xl yl lm ≤ 8 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n)) :=
  Q.BudP2.hp2Q

/-- **`BudClQ` from infra's `even` target alone** (rem: `Q.BudT.rem`; p2: `hp2Cl`; slow/obud/ocost: expmc) -/
theorem budClQ_of_e
    (heven : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
      clEQ 0 xl yl n ≤ 72 * BudQ.opC (max xl n) + yl * (320 * BudQ.opC (max xl n))) : BudClQ :=
  budClQ_of8 (fun xl n hx hn0 hn => Q.BudT.rem xl n hx hn0 hn) heven hp2Cl

end FvModexp.Arm64.IExp
