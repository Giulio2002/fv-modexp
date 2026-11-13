import FvModexp.Proofs.Arm64.ExpQ.Bridge
import FvModexp.Proofs.Arm64.Nat.RemDefs
import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false

/-!
# TIGHT COSTS — `BudQ.Targets.rem` for the bridged `nat.rem` cost (divmc s38; arm64 cost instances)

`IExp.clRQ 0 xl n = Q.brC (Q.NatDiv.costQ Q.drsCQ) NatRem.need 0 xl n` (Arm64/ExpQ/IExpClQ.lean): the Q-form budget of
`nat.div` (go-bigmodexpfix natdiv.go:520/590/750, asm's transcription in NatQ/DivHypQ) plus the stack reserve at the
level bound `17·xl + 68`. Proved: `≤ 4·opC (max xl n)` on the spec range (the `rem` field of `BudQ.Targets` /
`BudQ.TargetsM`; mirror worst 3.47 at `(xl, n) = (1, 1)`).
`drsCQ` is bounded crudely through two recursion levels (divisor `< 40` → `0`) with the proved P-form mul bounds
(Common/MulCostQB `mulCQ_le_B`): `drsCQ ul n ≤ 138550` for `ul ≤ 129`, `n ≤ 128` (exact max 22912); the slack at
`n ≥ 40` (where `opC` is ≥ 84 k) absorbs it.
-/

namespace FvModexp.Arm64.Q.BudT

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

/-- one recursion level: divisor `≤ 65` (its recursive call has divisor `< 40`) -/
theorem drsCQ_le1 {ul n : Nat} (hu : ul ≤ 129) (hn : n ≤ 65) : drsCQ ul n ≤ 5 * 1112 := by
  by_cases h40 : n < 40
  · rw [drsCQ_small h40]; exact Nat.zero_le _
  · rw [drsCQ_big h40, drsCQ_small (by omega), Nat.zero_add]
    exact Nat.mul_le_mul (steps_le hu h40) (mul_small (by omega) (by omega))

/-- **`drsCQ ul n ≤ 138550`** for `ul ≤ 129`, `n ≤ 128` -/
theorem drsCQ_le {ul n : Nat} (hu : ul ≤ 129) (hn : n ≤ 128) : drsCQ ul n ≤ 5 * (5 * 1112 + 22138) := by
  by_cases h40 : n < 40
  · rw [drsCQ_small h40]; exact Nat.zero_le _
  · rw [drsCQ_big h40]
    exact Nat.mul_le_mul (steps_le hu h40)
      (Nat.add_le_add (drsCQ_le1 hu (by omega)) (mul_mid (by omega) (by omega)))

/-- **`Targets.rem` for the bridged `nat.rem` cost** (`IExp.clRQ 0`) -/
theorem rem (xl n : Nat) (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) :
    Q.brC (Q.NatDiv.costQ Q.drsCQ) NatRem.need 0 xl n ≤ 4 * opC (max xl n) := by
  have hm1 := makeCost_le16 xl
  have hm2 := makeCost_le16 (xl + 1)
  have hm3 := makeCost_le16 (xl - n + 1)
  have hm4 : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
  have hd : drsCQ (xl + 1) n ≤ (if n < 40 then 0 else 5 * (5 * 1112 + 22138)) := by
    split
    · rw [drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact drsCQ_le (by omega) hn
  simp only [Q.brC, Q.NatDiv.costQ, Q.DivLarge.costQ, NatRem.need, stkRes, capB, potK, opC, allocCost]
  split at hd <;> omega

/-- the `rem` field in the shape of `BudQ.Targets` / `BudQ.TargetsM` -/
theorem rem_field : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 →
    (fun xl n => Q.brC (Q.NatDiv.costQ Q.drsCQ) NatRem.need 0 xl n) xl n ≤ 4 * opC (max xl n) :=
  fun xl n hx hn0 hn => rem xl n hx hn0 hn

end FvModexp.Arm64.Q.BudT
