import FvModexp.Proofs.Amd64.Top.RunLaDefs

/-! # `Run` (amd64): the operand-phase boundary `C0` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace FvModexp.Amd64.Run

/-- The operand phase (`getData` of base/exp/mod) starts here. -/
abbrev pcC0 : Nat := segAddr Extracted.program fn + 0x5c7

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run

/-- `CMPQ b, a; CMOVA` (unsigned "above": `¬ a < b` and `a - b ≠ 0` mod `2^64`) selects the maximum. -/
theorem cmova_max (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if ¬a < b ∧ ¬(18446744073709551616 - b + a) % 18446744073709551616 = 0 then a else b) = max a b := by
  by_cases h : a < b
  · rw [if_neg (by omega)]; omega
  · by_cases he : a = b
    · subst he; rw [if_neg (by intro h; apply h.2; omega)]; omega
    · rw [if_pos ⟨h, by omega⟩]; omega

end FvModexp.Amd64.Run
