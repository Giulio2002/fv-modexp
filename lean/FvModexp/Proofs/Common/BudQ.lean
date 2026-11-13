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
| term | owner | target (`W = opC (max xl n)`) | mirror `--bridge` (exact / with MulCostQB bounds) |
|---|---|---|---|
| `cR xl n` (nat.rem, bridged: `C + stkRes (17 xl + 68)`) | asm | `≤ 4·W` | 3.47 (n = 1) |
| `cS xl yl n` (expNNSlow, bridged) | expmc | `≤ makeCost xl + 8·W + yl·128·W` | 7.6 + yl·69 / 7.6 + yl·94 |
| `cE xl yl n` (expNNEven, incl. its supU) | infra | `≤ 72·W + yl·320·W` | 58 (n = 1) + yl·(208 / 271) |
| `cP xl yl lm` (expNNPowerOfTwo, `lm < 64n`) | infra | `≤ 6·W + yl·64·W` | 2.2 + yl·19 / 3.1 + yl·24 |
| `oB`, `oC` (windows OBud / OCost at the top) | expmc | `≤ 16·W` | 14.9 (n = 1) |
| `stkRes (Hr xl n)` (a top-level reserve, if any) | expmc | `≤ 14·W` | 13.9 (n = 1) |
Sum: setup `4 + 8 + 72 + 6 + 16 + 14 + 1 (the makeCosts) = 121 ≤ 128`, per exponent word `128 + 320 + 64 = 512`.
Numbers: `scripts/gen/exp-budget-terms.py --bridge [--qb]` (expmc s43's bridge model: only Slow is Q inside, the O(1)
callees are consumed through `C + stkRes (ℓ + D)` bridges, every top-level term at `ℓ = 0`). `budOK0`: the same without
the reserve term (the text of `IExp.BudCl` with the bridged instances at level `0`).
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
  rem : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → cR xl n ≤ 4 * opC (max xl n)
  slow : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → cS xl yl n ≤ makeCost xl + 8 * opC (max xl n) + yl * (128 * opC (max xl n))
  even : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → cE xl yl n ≤ 72 * opC (max xl n) + yl * (320 * opC (max xl n))
  p2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    cP xl yl lm ≤ 6 * opC (max xl n) + yl * (64 * opC (max xl n))
  obud : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oB n xl yl ≤ 16 * opC (max xl n)
  ocost : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oC n xl yl ≤ 16 * opC (max xl n)
  res : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → stkRes (Hr xl n) ≤ 14 * opC (max xl n)

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
    (hWW : W ≤ W') (hR : R ≤ 4 * W) (hS : S ≤ makeCost xl + 8 * W + yl * (128 * W))
    (hE : E ≤ 72 * W + yl * (320 * W)) (hP : P ≤ 6 * W + yl * (64 * W)) (hO : O ≤ 16 * W) (hH : Hs ≤ 14 * W) :
    24 + (makeCost 1 + makeCost n + R + (S + E) + P + O) + Hs ≤ (8 * (64 * yl) + 128) * W' := by
  have hm : 24 + makeCost 1 + makeCost n + makeCost xl ≤ W := by
    have := makeCost_le16 1; have := makeCost_le16 n; have := makeCost_le16 xl
    subst hW; unfold opC allocCost; omega
  have f1 : yl * (128 * W) = 128 * (yl * W) := Nat.mul_left_comm _ _ _
  have f2 : yl * (320 * W) = 320 * (yl * W) := Nat.mul_left_comm _ _ _
  have f3 : yl * (64 * W) = 64 * (yl * W) := Nat.mul_left_comm _ _ _
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

/-- **BudOK without a separate reserve term** (the text of `IExp.BudCl` with level-`0` bridged instances) -/
theorem budOK0 {cR : Nat → Nat → Nat} {cS cE cP oB oC : Nat → Nat → Nat → Nat} {Hr : Nat → Nat → Nat}
    (T : Targets cR cS cE cP oB oC Hr) :
    ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + cR xl n + (cS xl yl n + cE xl yl n) + cP xl yl lm + oB n xl yl) ≤
        ExpBudgetF (max (max xl yl) n) yl ∧
      24 + (makeCost 1 + makeCost n + cR xl n + (cS xl yl n + cE xl yl n) + cP xl yl lm + oC n xl yl) ≤
        ExpBudgetF (max (max xl yl) n) yl := by
  intro xl yl n lm hx hy hn0 hn hlm
  have h := budOK T xl yl n lm hx hy hn0 hn hlm
  unfold lhsB lhsC at h; omega


/-! ## Path-MAX shape (coordinator 2026-11-15 / "[infra s44]" request 1)

`nat.expNN` takes ONE of its branches (Slow / Even / P2 / the odd windows; `len y = 0` returns `1` before any), so its
charged cost can be the MAX over the branch costs instead of their sum (shape to be adopted by expmc's `NCost`/`NBudE`).
Then each branch gets the whole remaining allowance: `TargetsM` (setup: rem `4·W`, each branch `108·W`, reserve
`14·W`, the makeCosts `1·W`; per exponent word: each branch `512·W`). -/

/-- per-term targets for the path-MAX shape -/
structure TargetsM (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oB oC : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) : Prop where
  rem : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → cR xl n ≤ 4 * opC (max xl n)
  slow : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
    cS xl yl n ≤ makeCost xl + 108 * opC (max xl n) + yl * (512 * opC (max xl n))
  even : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → cE xl yl n ≤ 108 * opC (max xl n) + yl * (512 * opC (max xl n))
  p2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    cP xl yl lm ≤ 108 * opC (max xl n) + yl * (512 * opC (max xl n))
  obud : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oB n xl yl ≤ 108 * opC (max xl n) + yl * (512 * opC (max xl n))
  ocost : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → oC n xl yl ≤ 108 * opC (max xl n) + yl * (512 * opC (max xl n))
  res : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 → stkRes (Hr xl n) ≤ 14 * opC (max xl n)

/-- the path-MAX budget text: the common prefix (`x mod m`, the result words) + the MAX over the four branches -/
def lhsM (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oX : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) (xl yl n lm : Nat) : Nat :=
  24 + (makeCost 1 + makeCost n + cR xl n + max (max (cS xl yl n) (cE xl yl n)) (max (cP xl yl lm) (oX n xl yl))) +
    stkRes (Hr xl n)

private theorem sumM_le {xl yl n W W' R S E P O Hs : Nat} (hx : xl ≤ 128) (hn : n ≤ 128) (hW : W = opC (max xl n))
    (hWW : W ≤ W') (hR : R ≤ 4 * W) (hS : S ≤ makeCost xl + 108 * W + yl * (512 * W))
    (hE : E ≤ 108 * W + yl * (512 * W)) (hP : P ≤ 108 * W + yl * (512 * W)) (hO : O ≤ 108 * W + yl * (512 * W))
    (hH : Hs ≤ 14 * W) :
    24 + (makeCost 1 + makeCost n + R + max (max S E) (max P O)) + Hs ≤ (8 * (64 * yl) + 128) * W' := by
  have hm : 24 + makeCost 1 + makeCost n + makeCost xl ≤ W := by
    have := makeCost_le16 1; have := makeCost_le16 n; have := makeCost_le16 xl
    subst hW; unfold opC allocCost; omega
  have f1 : yl * (512 * W) = 512 * (yl * W) := Nat.mul_left_comm _ _ _
  have f4 : (8 * (64 * yl) + 128) * W' = 8 * (64 * (yl * W')) + 128 * W' := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  have f5 : yl * W ≤ yl * W' := Nat.mul_le_mul_left _ hWW
  rw [f4]; rw [f1] at hS hE hP hO
  have : max (max S E) (max P O) ≤ makeCost xl + 108 * W + 512 * (yl * W) := by omega
  omega

/-- **BudOK, path-MAX shape** (both inequalities; `oB` = OBud for the budget premise, `oC` = OCost for the charge) -/
theorem budOKM {cR : Nat → Nat → Nat} {cS cE cP oB oC : Nat → Nat → Nat → Nat} {Hr : Nat → Nat → Nat}
    (T : TargetsM cR cS cE cP oB oC Hr) :
    ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      lhsM cR cS cE cP oB Hr xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl ∧
      lhsM cR cS cE cP oC Hr xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl := by
  intro xl yl n lm hx hy hn0 hn hlm
  have hWW : opC (max xl n) ≤ opC (max (max xl yl) n) := opC_mono (by omega)
  exact ⟨sumM_le hx hn rfl hWW (T.rem xl n hx hn0 hn) (T.slow xl yl n hx hy hn0 hn) (T.even xl yl n hx hy hn0 hn)
      (T.p2 xl yl n lm hx hy hn0 hn hlm) (T.obud xl yl n hx hy hn0 hn) (T.res xl n hx hn0 hn),
    sumM_le hx hn rfl hWW (T.rem xl n hx hn0 hn) (T.slow xl yl n hx hy hn0 hn) (T.even xl yl n hx hy hn0 hn)
      (T.p2 xl yl n lm hx hy hn0 hn hlm) (T.ocost xl yl n hx hy hn0 hn) (T.res xl n hx hn0 hn)⟩

/-- the sum shape's targets imply the path-MAX ones (so a cost proved against `Targets` also serves `TargetsM`) -/
theorem Targets.toM {cR : Nat → Nat → Nat} {cS cE cP oB oC : Nat → Nat → Nat → Nat} {Hr : Nat → Nat → Nat}
    (T : Targets cR cS cE cP oB oC Hr) : TargetsM cR cS cE cP oB oC Hr := by
  refine ⟨fun xl n a b c => T.rem xl n a b c, fun xl yl n a b c d => ?_, fun xl yl n a b c d => ?_,
    fun xl yl n lm a b c d e => ?_, fun xl yl n a b c d => ?_, fun xl yl n a b c d => ?_, T.res⟩
  · have h := T.slow xl yl n a b c d
    have : yl * (128 * opC (max xl n)) ≤ yl * (512 * opC (max xl n)) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have h := T.even xl yl n a b c d
    have : yl * (320 * opC (max xl n)) ≤ yl * (512 * opC (max xl n)) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have h := T.p2 xl yl n lm a b c d e
    have : yl * (64 * opC (max xl n)) ≤ yl * (512 * opC (max xl n)) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have h := T.obud xl yl n a b c d; omega
  · have h := T.ocost xl yl n a b c d; omega

/-- the gate number: `ExpBudgetF 128 128 ≤ 2 ^ 35` (32 GiB; coordinator 2026-11-15) -/
theorem gate : ExpBudgetF 128 128 ≤ 2 ^ 35 := by decide

end FvModexp.BudQ
