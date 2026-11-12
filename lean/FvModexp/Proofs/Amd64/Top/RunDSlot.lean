import FvModexp.Proofs.Amd64.Top.RunDRel

set_option autoImplicit false

/-! # `Run` (amd64): operand-slot transport from ONE read fact (agent top s20, speed)

`OpDone.transport` / `OpsApart.transport` take four / two read equalities per operand; at the end of a D segment each was
closed by its own `janus_simp [opAt]` on the segment's big context (≈ 4 s each, 12 per segment). Here the reads come from a
single fact about the operand slots `[opAt s (k - 1), opAt s 0 + 32)` (proved once per segment). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- the slots of operands `0 … k - 1` read the same in `m'` as in `m` -/
def SlotsEq (m m' : Janus.Arm64.Memory) (s : State) (k : Nat) : Prop :=
  ∀ a n, opAt s (k - 1) ≤ a → a + n ≤ opAt s 0 + 32 → m'.readLE a n = m.readLE a n

theorem OpDone.transportS {R : RtInv} {m m' : Janus.Arm64.Memory} {s : State} {p len : BitVec 64} {L L1 L2 : List (Nat × Nat)}
    {j k : Nat} (h : OpDone R m s p len L L1 j) (hj : j < k) (hr : SlotsEq m m' s k)
    (hLF : LiveFrame m m' L1 []) (hsub : ∀ a n, InRanges a n L1 → InRanges a n L2) : OpDone R m' s p len L L2 j := by
  refine OpDone.transport h ?_ ?_ ?_ ?_ hLF hsub
  · exact hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega)
  · exact hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega)
  · exact hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega)
  · exact hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega)

theorem OpsApart.transportS {m M : Janus.Arm64.Memory} {s : State} {k : Nat} (h : OpsApart m s k) (hr : SlotsEq m M s k) :
    OpsApart M s k :=
  OpsApart.transport h fun i hi =>
    ⟨hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega),
      hr _ _ (by simp only [opAt]; omega) (by simp only [opAt]; omega)⟩

end FvModexp.Amd64.Run
