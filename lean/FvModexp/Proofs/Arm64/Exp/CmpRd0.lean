import FvModexp.Proofs.Arm64.Exp.RdIn0

/-!
# `nat.cmp` (arm64) with empty-tolerant operands (`RdIn0`, coordinator decision on "[infra s30] FINDING"; agent asm)

asm's `nat.cmp` summary (`CmpSum.cmp_summary`, `CmpW.sum` / `CmpW.pre_of`) already accepts an empty operand with an
arbitrary pointer (`SliceOK`: `n = 0 ∨ …`), for both operands. `RdIn0.cmpOK` turns a caller's `RdIn0` operand fact
into exactly the operand premise of `CmpW.pre_of` (window `stk ≥ 24`, `above ≥ 40`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpHyp

theorem RdIn0.cmpOK {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above p n : Nat}
    (h : RdIn0 R L s stk above p n) (hk : 24 ≤ stk) (ha : 40 ≤ above) (hsp : 24 ≤ s.sp.toNat) :
    n = 0 ∨ (p + 8 * n ≤ 2 ^ 48 ∧ s.mem.accessible p (8 * n) false = true ∧
      Apart p (8 * n) (s.sp.toNat - 24) 64) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact Or.inl h0
  · obtain ⟨-, hacc, h48, -, hw⟩ := h.2 h0
    simp only [win, outside_cons, outside_nil, and_true] at hw
    exact Or.inr ⟨h48, hacc, by unfold Apart; omega⟩

end FvModexp.Arm64.ExpHyp
