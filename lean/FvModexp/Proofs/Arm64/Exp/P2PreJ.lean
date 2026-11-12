import FvModexp.Proofs.Arm64.Exp.P2PrePw

/-!
# `buildPrecomputationWindowModPower2` (arm64): the main loop's join (agent infra)

`HeadJ … i`: from the loop head `0x1b567c` with `i` (even, `2 ≤ i ≤ pl`), the context, `powers[j]` computed for
`j < i` and untouched (`PwT`) for `i ≤ j < pl`, the budget spent so far, the function returns with the postcondition.
`Lo`: the loop's local slots of round `i`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

/-- the loop head -/
abbrev pcH : Nat := 1791612

/-- the round's locals: `i` at `sp - 88`, `24 i` at `sp - 72`, `24 i + 24` at `sp - 80`, `&powers[i]` at `sp - 16` -/
@[reducible] def Lo (s : State) (pw i : Nat) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 88) 8 = i ∧ M.readLE (s.sp.toNat - 72) 8 = 24 * i ∧
    M.readLE (s.sp.toNat - 80) 8 = 24 * i + 24 ∧ M.readLE (s.sp.toNat - 16) 8 = pw + 24 * i

def HeadJ (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    S.pc = BitVec.ofNat 64 pcH → S.sp = BitVec.ofNat 64 (s.sp.toNat - 208) → S.regs 28 = s.regs 28 →
    S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216) → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 i → S.regs 7 = BitVec.ofNat 64 pw → S.regs 9 = BitVec.ofNat 64 (W lm) →
    Ctx R kc L st pw pl lm s bp S.mem L1 b1 →
    (∀ j, j < i → PwD S.mem pw bp lm (natVal s.mem x xl) j) → (∀ j, i ≤ j → j < pl → PwT S.mem pw bp lm j) →
    i % 2 = 0 → 2 ≤ i → i ≤ pl → b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm) ≤ b1 →
    Goal impl R kc sqC mlC b L st pw pl lm x xl s S

end FvModexp.Arm64.P2Pre
