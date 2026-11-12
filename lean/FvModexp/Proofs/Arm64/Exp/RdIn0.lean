import FvModexp.Proofs.Arm64.Exp.ExpHyp

/-!
# arm64 `RdIn0`: the empty-tolerant read-only input (coordinator decision on "[infra s30] FINDING"; agent expmc)

A zero-length operand (e.g. a nil `nat` returned by `nat.expNN`) carries no location fact. Twin of
`FvModexp.Amd64.EvenHyp.RdIn0`; in `ExpHyp`'s namespace next to arm64's `RdIn`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpHyp

@[reducible] def RdIn0 (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above p n : Nat) : Prop :=
  n < 2 ^ 40 ∧ (0 < n → RdIn R L s stk above p n)

theorem RdIn.toRdIn0 {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above p n : Nat}
    (h : RdIn R L s stk above p n) : RdIn0 R L s stk above p n := ⟨h.1, fun _ => h⟩

theorem RdIn0.toRdIn {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above p n : Nat}
    (h : RdIn0 R L s stk above p n) (hn : 0 < n) : RdIn R L s stk above p n := h.2 hn

end FvModexp.Arm64.ExpHyp
