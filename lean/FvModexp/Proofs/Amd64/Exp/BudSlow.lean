import FvModexp.Proofs.Amd64.Exp.SlowQStmt
import FvModexp.Proofs.Amd64.Exp.DrsCQB
import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false

/-!
# TIGHT COSTS BudOK: `Targets.slow` for expmc's bridged `nat.expNNSlow` cost (agent expmc s83: amd64 copy of arm64 ExpQ/BudSlowQ, s44)

`slow_target`: the bridged Q-form cost of `nat.expNNSlow` at level `0` (`EvenRow.cS 0 xl yl n`) is at most
`makeCost xl + 8·W + yl·(128·W)`, `W = BudQ.opC (max xl n)` (divmc's `BudQ.Targets.slow`). Per round
(`64` per exponent word): `sup sqrCQ ≤ 128 M + 808`, `sup mulCQ ≤ 1554 M + 3968` (MulCostQB), `sup nat.div ≤ 1912 M + 2296`
(DrsCQB; `0` drs term for `n < 40`), together `≤ 2 W`; the reserve `stkRes (48 M + 64) ≤ 8 W`.
-/

namespace FvModexp.Amd64.Q.ExpSlow

open FvModexp.Exp (supN)

theorem supN_le_const (f : Nat → Nat) (B : Nat) : ∀ n, (∀ j, j ≤ n → f j ≤ B) → supN f n ≤ B := by
  intro n
  induction n with
  | zero => intro h; exact h 0 (Nat.le_refl _)
  | succ n ih => intro h; exact Nat.max_le.2 ⟨ih fun j hj => h j (by omega), h _ (Nat.le_refl _)⟩

theorem sq_le {M : Nat} (hM : M ≤ 128) : supN sqrCQ M ≤ 128 * M + 808 := by
  refine supN_le_const _ _ M fun j hj => ?_
  have := sqrCQ_le_B (n := j) (by omega); unfold sqrCB at this; split at this
  · omega
  · split at this <;> omega

theorem mul_le {M xl : Nat} (hM : M ≤ 128) (hx : xl ≤ M) :
    supN (fun j => mulCQ j xl) (2 * M) ≤ 1554 * M + 3968 := by
  refine supN_le_const _ _ (2 * M) fun j hj => ?_
  have := mulCQ_le_B (xl := j) (yl := xl) (by omega)
  have h1 : max j xl ≤ 2 * M := by omega
  have h2 : min j xl ≤ M := by omega
  generalize max j xl = a at this h1; generalize min j xl = c at this h2
  unfold mulCB at this; split at this
  · omega
  · split at this <;> omega

theorem div_le {M n : Nat} (hM : M ≤ 128) (hn : n ≤ M) :
    supN (fun j => NatDiv.costQ drsCQ j n) (3 * M) ≤ (if n < 40 then 0 else 1824 * M + 88 * n + 1960) + 144 * M + 336 := by
  refine supN_le_const _ _ (3 * M) fun j hj => ?_
  simp only [NatDiv.costQ, DivLarge.costQ]
  have m1 := BudQ.makeCost_le16 j; have m2 := BudQ.makeCost_le16 (j + 1); have m3 := BudQ.makeCost_le16 (j - n + 1)
  have m4 : makeCost 1 = 40 := by decide
  by_cases h40 : n < 40
  · rw [drsCQ_small h40, if_pos h40]; omega
  · rw [if_neg h40]; have := drsCQ_le (U := j + 1) (n := n) (by omega) (by omega); omega

/-- **`Targets.slow`** for the bridged Q-form cost of `nat.expNNSlow` -/
theorem slow_target {xl yl n : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) :
    slowBr (costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) needH 0 xl yl n ≤
      makeCost xl + 8 * BudQ.opC (max xl n) + yl * (128 * BudQ.opC (max xl n)) := by
  simp only [slowBr, costQ, needH, Nat.zero_add]
  have hS := sq_le (M := max xl n) (by omega)
  have hM := mul_le (M := max xl n) (xl := xl) (by omega) (by omega)
  have hD := div_le (M := max xl n) (n := n) (by omega) (by omega)
  have hW : BudQ.opC (max xl n) = 2048 * max xl n + 2072 := by unfold BudQ.opC allocCost; omega
  rw [hW]
  have hnM : n ≤ max xl n := Nat.le_max_right _ _
  have hxM : xl ≤ max xl n := Nat.le_max_left _ _
  have hM8 : max xl n ≤ 128 := by omega
  generalize max xl n = M at hS hM hD hnM hxM hM8 ⊢
  have hM1 : 1 ≤ M := by omega
  have hsum : supN sqrCQ M + supN (fun j => mulCQ j xl) (2 * M) + supN (fun j => NatDiv.costQ drsCQ j n) (3 * M) ≤
      2 * (2048 * M + 2072) := by
    by_cases h40 : n < 40
    · rw [if_pos h40] at hD; omega
    · rw [if_neg h40] at hD; omega
  have hm : 64 * yl * (supN sqrCQ M + supN (fun j => mulCQ j xl) (2 * M) +
      supN (fun j => NatDiv.costQ drsCQ j n) (3 * M)) ≤ yl * (128 * (2048 * M + 2072)) := by
    rw [Nat.mul_comm 64 yl, Nat.mul_assoc]; exact Nat.mul_le_mul_left yl (by omega)
  have hr : stkRes (48 * M + 64) = 7680 * M + 10680 := by unfold stkRes capB potK; omega
  rw [hr]; omega

end FvModexp.Amd64.Q.ExpSlow
