import FvModexp.Proofs.Common.MulCostQB

set_option autoImplicit false

/-!
# BudOK skeleton for the TIGHT-COSTS release budget (divmc s37; ISA independent)

The release gate (BRIEF "TIGHT COSTS"; NOTES-conventions "[coordinator] 2026-11-15") is the FACTOR-FREE allowance
`ExpBudgetF w yW = (8·(64·yW) + 128)·opC w` (`opC w = allocCost (1024 w + 1024)` = `RunIface.opCost w`), i.e. a setup
part `128·opC w` and `512·opC w` per exponent word. This module proves the BudOK inequalities (same TEXT as
`Run.Closed.BudOK` / `IExp.BudCl`, Arm64/Exp/IExpCl.lean, with every cost level-free — the Q-form — and the stack
reserve `stkRes H` paid once by the stack owner `(*Int).exp`) from PER-TERM TARGETS, one per owner, stated as the
fields of `Targets` (hypotheses until the owners' Q-cost modules land; nothing here is assumed elsewhere):
| term | owner | target (`W = opC (max xl n)`) | mirror (exact Q costs / with the MulCostQB bounds) |
|---|---|---|---|
| `cR xl n` (nat.rem) | asm | `≤ W` | 0.07 / 0.11 |
| `cS xl yl n` (expNNSlow) | expmc | `≤ makeCost xl + yl·128·W` | per yl 69 / 108 |
| `cE xl yl n` (expNNEven) | infra | `≤ 48·W + yl·336·W` | 12 + 184 / 21 + 287 |
| `cP xl yl lm` (expNNPowerOfTwo, `lm < 64n`) | infra | `≤ 16·W + yl·48·W` | 2.2 + 19 / 4.5 + 33 |
| `oB`, `oC` (windows OBud / OCost) | expmc | `≤ 2·W` | 0.56 / 0.81 |
| `stkRes (Hr xl n)` (the one stack reserve) | expmc | `≤ 16·W` | 13.9 (at n = 1) |
Sum: setup `1 + 48 + 16 + 2 + 16 + 1 (the makeCosts) = 84 ≤ 128`, per exponent word `128 + 336 + 48 = 512`.
The mul/sqr kernels inside these terms have closed bounds in Common/MulCostQB (`mulCB`, `sqrCB`, `mulCQ_le_op`, …).
-/

namespace FvModexp.BudQ

/-- `RunIface.opCost` (same body; Top/RunIface is a heavy module, so the skeleton restates it) -/
def opC (w : Nat) : Nat := allocCost (1024 * w + 1024)

/-- **the factor-free release allowance** (`RunIface.ExpBudget` without the temporary `2^32` slack) -/
def ExpBudgetF (w yW : Nat) : Nat := (8 * (64 * yW) + 128) * opC w

theorem opC_mono {w w' : Nat} (h : w ≤ w') : opC w ≤ opC w' := by unfold opC allocCost; omega

/-- the per-term targets (see the module doc); `cR xl n`, `cS/cE xl yl n`, `cP xl yl lm`, `oB/oC n xl yl`, `Hr xl n` -/
structure Targets (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oB oC : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) : Prop where
  rem : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → cR xl n ≤ opC (max xl n)
  slow : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → cS xl yl n ≤ makeCost xl + yl * (128 * opC (max xl n))
  even : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → cE xl yl n ≤ 48 * opC (max xl n) + yl * (336 * opC (max xl n))
  p2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    cP xl yl lm ≤ 16 * opC (max xl n) + yl * (48 * opC (max xl n))
  obud : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oB n xl yl ≤ 2 * opC (max xl n)
  ocost : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oC n xl yl ≤ 2 * opC (max xl n)
  res : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → stkRes (Hr xl n) ≤ 16 * opC (max xl n)

/-- the budget premise of `nat.expNN` at the top (as `NPre`'s, level-free) + the stack reserve -/
def lhsB (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oB : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) (xl yl n lm : Nat) : Nat :=
  24 + (makeCost 1 + makeCost n + cR xl n + (cS xl yl n + cE xl yl n) + cP xl yl lm + oB n xl yl) + stkRes (Hr xl n)

/-- the charged cost of `nat.expNN` at the top (as `NCost`, level-free) + the stack reserve -/
def lhsC (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oC : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) (xl yl n lm : Nat) : Nat :=
  24 + (makeCost 1 + makeCost n + cR xl n + (cS xl yl n + cE xl yl n) + cP xl yl lm + oC n xl yl) + stkRes (Hr xl n)

theorem makeCost_le16 (k : Nat) : makeCost k ≤ 16 * k + 88 := by
  unfold makeCost makeCap allocCost; split <;> omega

private theorem sum_le {xl yl n W W' R S E P O Hs : Nat} (hx : xl ≤ 128) (hn : n ≤ 128) (hW : W = opC (max xl n))
    (hWW : W ≤ W') (hR : R ≤ W) (hS : S ≤ makeCost xl + yl * (128 * W)) (hE : E ≤ 48 * W + yl * (336 * W))
    (hP : P ≤ 16 * W + yl * (48 * W)) (hO : O ≤ 2 * W) (hH : Hs ≤ 16 * W) :
    24 + (makeCost 1 + makeCost n + R + (S + E) + P + O) + Hs ≤ (8 * (64 * yl) + 128) * W' := by
  have hm : 24 + makeCost 1 + makeCost n + makeCost xl ≤ W := by
    have := makeCost_le16 1; have := makeCost_le16 n; have := makeCost_le16 xl
    subst hW; unfold opC allocCost; omega
  have f1 : yl * (128 * W) = 128 * (yl * W) := Nat.mul_left_comm _ _ _
  have f2 : yl * (336 * W) = 336 * (yl * W) := Nat.mul_left_comm _ _ _
  have f3 : yl * (48 * W) = 48 * (yl * W) := Nat.mul_left_comm _ _ _
  have f4 : (8 * (64 * yl) + 128) * W' = 8 * (64 * (yl * W')) + 128 * W' := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  have f5 : yl * W ≤ yl * W' := Nat.mul_le_mul_left _ hWW
  rw [f4]; rw [f1] at hS; rw [f2] at hE; rw [f3] at hP
  omega

/-- **BudOK from the per-term targets**: both inequalities of `Run.Closed.BudOK` (level-free text + `stkRes`) hold
against the factor-free allowance on the whole spec range -/
theorem budOK {cR : Nat → Nat → Nat} {cS cE cP oB oC : Nat → Nat → Nat → Nat} {Hr : Nat → Nat → Nat}
    (T : Targets cR cS cE cP oB oC Hr) :
    ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      lhsB cR cS cE cP oB Hr xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl ∧
      lhsC cR cS cE cP oC Hr xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl := by
  intro xl yl n lm hx hy hn0 hn hlm
  have hWW : opC (max xl n) ≤ opC (max (max xl yl) n) := opC_mono (by omega)
  refine ⟨?_, ?_⟩
  · exact sum_le hx hn rfl hWW (T.rem xl n hx hn0 hn) (T.slow xl yl n hx hy hn0 hn) (T.even xl yl n hx hy hn0 hn)
      (T.p2 xl yl n lm hx hy hn0 hn hlm) (T.obud xl yl n hx hy hn0 hn) (T.res xl n hx hn0 hn)
  · exact sum_le hx hn rfl hWW (T.rem xl n hx hn0 hn) (T.slow xl yl n hx hy hn0 hn) (T.even xl yl n hx hy hn0 hn)
      (T.p2 xl yl n lm hx hy hn0 hn hlm) (T.ocost xl yl n hx hy hn0 hn) (T.res xl n hx hn0 hn)

/-- the gate number: `ExpBudgetF 128 128 ≤ 2 ^ 35` (32 GiB; coordinator 2026-11-15) -/
theorem gate : ExpBudgetF 128 128 ≤ 2 ^ 35 := by decide

end FvModexp.BudQ
