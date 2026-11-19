import FvModexp.Spec.Amd64.Run

set_option autoImplicit false

/-!
# Row 1, amd64: the success budget over the whole spec range (agent asm s77, REDTEAM-arm64 R5)

`okBudget_gate`: for every call data that passes EIP-7823 (`LengthsPass`: every length header ≤ 1024), the budget
`Spec.RunAmd64.okBudget (parseLengths data)` that amd64 `RunSucc.correctness` demands is at most `2^35` bytes (32 GiB) — the
release gate "TIGHT COSTS" (a) on the statement's own budget, not only on its `exp` part (twin of `Arm64/Top/RunGate.lean`; `Spec.RunAmd64.okBudget` is the same formula).
`okBudget` is monotone in the lengths; its value at the corner (all three lengths 1024) is `okBudget_corner`
(17 366 406 472 ≈ 1.737e10 < 2^35 ≈ 3.436e10). Pure arithmetic: `omega` / `decide`. Also `errBudget_le_okBudget` (the error path's 512 bytes ≤ every success budget).
-/

namespace FvModexp.Amd64.RunGate


open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

/-- the budget at the corner of the spec range (base = exponent = modulus = 1024 bytes) -/
theorem okBudget_corner : RunAmd64.okBudget ⟨1024, 1024, 1024⟩ = 17366406472 := by decide

/-- the corner bound with the two multiplied quantities as atoms (`o` = the per-request block bound, `x` = the `exp`
request count) -/
theorem corner_aux (o x : Nat) (ho : o ≤ 264216) (hx : x ≤ 65664) :
    456 + 3 * (2072 + 2136) + (64 * o + x * o + 2072) + 2072 ≤ 17366406472 := by
  have h2 : x * o ≤ 65664 * 264216 := Nat.mul_le_mul hx ho
  omega

/-- `okBudget` is monotone: lengths at most 1024 give at most the corner value (`okBudget_corner`) -/
theorem okBudget_le_corner (l : Lengths) (hb : l.base ≤ 1024) (he : l.exponent ≤ 1024) (hm : l.modulus ≤ 1024) :
    RunAmd64.okBudget l ≤ 17366406472 := by
  have hw : max (max ((l.base + 7) / 8) ((l.exponent + 7) / 8)) ((l.modulus + 7) / 8) ≤ 128 := by
    simp only [Nat.max_le]; omega
  exact corner_aux _ _ (by unfold RunAmd64.blockBound; omega) (by omega)

/-- **The release gate on the row-1 success budget**: for every call data passing EIP-7823, `okBudget ≤ 2^35`. -/
theorem okBudget_gate (data : ByteArray) (h : LengthsPass data) :
    RunAmd64.okBudget (parseLengths data) ≤ 2 ^ 35 := by
  have ⟨hb, he, hm⟩ := (lengthsPass_iff data).1 h
  have hc := okBudget_le_corner (parseLengths data) hb he hm
  have : (17366406472 : Nat) ≤ 2 ^ 35 := by decide
  omega

/-- the error-path budget (`ErrReqs`) is below every success budget: `3 · blockBound 64 + blockBound 16 = 512` -/
theorem errBudget_le_okBudget (l : Lengths) :
    3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16 ≤ RunAmd64.okBudget l :=
  Nat.le_trans (Nat.add_le_add_left (by decide : RunAmd64.blockBound 16 ≤
      3 * (RunAmd64.blockBound 1024 + RunAmd64.blockBound (8 * 132))) _)
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

end FvModexp.Amd64.RunGate
