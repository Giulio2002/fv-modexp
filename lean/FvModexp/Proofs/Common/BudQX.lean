import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false

/-!
# BudOK skeleton — expmc's nat.expNN PATH-MAX text (divmc s38; ISA independent)

expmc s44 ("[expmc s44] ANNOUNCE — nat.expNN PATH-MAX budget", NOTES-conventions) states `ExpN.NPre`'s budget conjunct
and `ExpN.NCost` as (go-bigmodexpfix nat.go:639-720: `setWord`, `z.rem` when `y = 1`, else `z.make(len m)` + ONE of
Slow / Even / P2 / odd windows; the `(*Int).exp` costS slot = `max clS clE`)
`makeCost 1 + max (costR xl n) (makeCost n + max (max costS costE) (max costP (OBud | OCost)))`.
`lhsX` is that text (level `0`, the `24`-byte prefix as in `IExp.BudCl`); it is `≤ lhsM` (the rem cost is a summand
there instead of a max operand), so the path-MAX targets `TargetsM` give both BudOK inequalities (`budOKX`).
-/

namespace FvModexp.BudQ

/-- expmc's path-MAX budget text (no separate reserve: the bridged instances carry their reserves) -/
def lhsX (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oX : Nat → Nat → Nat → Nat)
    (xl yl n lm : Nat) : Nat :=
  24 + (makeCost 1 + max (cR xl n) (makeCost n + max (max (cS xl yl n) (cE xl yl n)) (max (cP xl yl lm) (oX n xl yl))))

theorem lhsX_le_lhsM (cR : Nat → Nat → Nat) (cS cE cP : Nat → Nat → Nat → Nat) (oX : Nat → Nat → Nat → Nat)
    (Hr : Nat → Nat → Nat) (xl yl n lm : Nat) :
    lhsX cR cS cE cP oX xl yl n lm ≤ lhsM cR cS cE cP oX Hr xl yl n lm := by
  unfold lhsX lhsM; omega

/-- **BudOK, expmc's path-MAX text** (`oB` = OBud for the budget premise, `oC` = OCost for the charge) -/
theorem budOKX {cR : Nat → Nat → Nat} {cS cE cP oB oC : Nat → Nat → Nat → Nat} {Hr : Nat → Nat → Nat}
    (T : TargetsM cR cS cE cP oB oC Hr) :
    ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      lhsX cR cS cE cP oB xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl ∧
      lhsX cR cS cE cP oC xl yl n lm ≤ ExpBudgetF (max (max xl yl) n) yl := by
  intro xl yl n lm hx hy hn0 hn hlm
  have h := budOKM T xl yl n lm hx hy hn0 hn hlm
  exact ⟨Nat.le_trans (lhsX_le_lhsM cR cS cE cP oB Hr xl yl n lm) h.1,
    Nat.le_trans (lhsX_le_lhsM cR cS cE cP oC Hr xl yl n lm) h.2⟩

/-- the reserve field is free when there is no top-level reserve (`Hr = 0`) -/
theorem res_zero : ∀ xl n, xl ≤ 128 → 0 < n → n ≤ 128 →
    stkRes ((fun _ _ => 0 : Nat → Nat → Nat) xl n) ≤ 14 * opC (max xl n) := by
  intro xl n _ _ _; simp only [stkRes, capB, potK, opC, allocCost]; omega

end FvModexp.BudQ
