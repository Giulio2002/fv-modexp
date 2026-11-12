import FvModexp.Proofs.Amd64.Exp.RdIn0

/-!
# `nat.cmp` (amd64) with empty-tolerant operands (`RdIn0`, coordinator decision on "[infra s30] FINDING"; agent asm)

asm's amd64 `nat.cmp` summary (`CmpSum`, `CmpW.sum`) already accepts an empty operand with an arbitrary pointer
(`SliceOK`: `n = 0 ∨ …`), for both operands. `RdIn0.cmpOK` turns a caller's `RdIn0` operand fact into that operand
premise (window `stk ≥ 8`, `above ≥ 40`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.EvenHyp

theorem RdIn0.cmpOK {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above p n : Nat}
    (h : RdIn0 R L s stk above p n) (hk : 8 ≤ stk) (ha : 40 ≤ above) (hsp : 8 ≤ (s.regs 4).toNat) :
    n = 0 ∨ (p + 8 * n ≤ 2 ^ 48 ∧ s.mem.accessible p (8 * n) false = true ∧
      Apart p (8 * n) ((s.regs 4).toNat - 8) 48) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact Or.inl h0
  · obtain ⟨-, hacc, h48, -, hw⟩ := h.2 h0
    simp only [win, outside_cons, outside_nil, and_true] at hw
    exact Or.inr ⟨h48, hacc, by unfold Apart; omega⟩

end FvModexp.Amd64.EvenHyp
