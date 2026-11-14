import FvModexp.Proofs.Amd64.Exp.NHyp

set_option autoImplicit false

/-!
# amd64 ROW-form stack arguments (agent divmc s80)

Janus v0.3.3's audit rejects a row precondition with a memory read whose address mentions `RSP` but is not literally
`(RSP).toNat + k` with a numeral `k ≥ 8` (the conservative `[RSP]`-word rule). `NHyp.StkArg s k p l c` reads
`RSP + k + 8 …`: after the audit expands it (`k = 0` / `k = 24`) the addresses are `RSP + 0 + 8`, `RSP + 24 + 8`, …
(nested arithmetic) and the row is refused, although these are stack arguments, not the return address.
`StkArg0` / `StkArg24` state the same facts with flat numeral offsets; a row precondition uses them and its proof
converts with `StkArg0.toStkArg` / `StkArg24.toStkArg` (and back, for the witnesses).
-/

open Janus Janus.Amd64 FvModexp

namespace FvModexp.Amd64.NHyp

/-- `StkArg s 0 p l c` in the audit-accepted form: the words at `RSP + 8`, `RSP + 16`, `RSP + 24` -/
def StkArg0 (s : State) (p l c : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = p ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = l ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = c

/-- `StkArg s 24 p l c` in the audit-accepted form: the words at `RSP + 32`, `RSP + 40`, `RSP + 48` -/
def StkArg24 (s : State) (p l c : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 32) 8 = p ∧ s.mem.readLE ((s.regs 4).toNat + 40) 8 = l ∧
    s.mem.readLE ((s.regs 4).toNat + 48) 8 = c

theorem StkArg0.toStkArg {s : State} {p l c : Nat} (h : StkArg0 s p l c) : StkArg s 0 p l c := by
  simp only [StkArg, Nat.add_zero]; exact h

theorem StkArg0.of_stkArg {s : State} {p l c : Nat} (h : StkArg s 0 p l c) : StkArg0 s p l c := by
  simp only [StkArg, Nat.add_zero] at h; exact h

theorem StkArg24.toStkArg {s : State} {p l c : Nat} (h : StkArg24 s p l c) : StkArg s 24 p l c := by
  simp only [StkArg, Nat.add_assoc, Nat.reduceAdd]; exact h

theorem StkArg24.of_stkArg {s : State} {p l c : Nat} (h : StkArg s 24 p l c) : StkArg24 s p l c := by
  simp only [StkArg, Nat.add_assoc, Nat.reduceAdd] at h; exact h

end FvModexp.Amd64.NHyp
