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

/-- `&powers[i+1]` at `sp - 24` (stored after the round's `sqr`) -/
@[reducible] def Lo2 (s : State) (pw i : Nat) (M : Memory) : Prop := M.readLE (s.sp.toNat - 24) 8 = pw + 24 * i + 24

/-- the round facts at memory `M` while `powers[k]` is computed in round `i` -/
structure RS (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm : Nat) (s : State) (X bp : Nat) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) (i k : Nat) : Prop where
  c : Ctx R kc L st pw pl lm s bp M L1 b1
  d : ∀ j, j < k → PwD M pw bp lm X j
  t : ∀ j, k < j → j < pl → PwT M pw bp lm j
  lo : Lo s pw i M

/-- the generic join inside round `i`, after a call whose result `(bp + 8 k w, l, 2 w)` (`k = kf i`) belongs to
`powers[k]`: value `v i`, `l ≤ lb`, budget spent `c0 + (i/2 - 1) rc + cst` -/
def JX (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (pc : Nat) (E : Nat → Memory → Prop)
    (kf v : Nat → Nat) (lb cst : Nat) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 l : Nat),
    S.pc = BitVec.ofNat 64 pc → S.sp = BitVec.ofNat 64 (s.sp.toNat - 208) → S.regs 28 = s.regs 28 →
    S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216) → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm)) → S.regs 1 = BitVec.ofNat 64 l →
    S.regs 2 = BitVec.ofNat 64 (2 * W lm) →
    RS R kc L st pw pl lm s (natVal s.mem x xl) bp S.mem L1 b1 i (kf i) → E i S.mem → l ≤ lb →
    natVal S.mem (bp + 8 * (kf i * W lm)) l = v i → NatNorm S.mem (bp + 8 * (kf i * W lm)) l →
    i % 2 = 0 → 2 ≤ i → i + 2 ≤ pl →
    b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm + cst) ≤ b1 →
    Goal impl R kc sqC mlC b L st pw pl lm x xl s S

section
variable (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State)

/-- the value of `powers[j]` -/
abbrev PV (j : Nat) : Nat := Exp.p2Pow lm (natVal s.mem x xl) j

/-- after `sqr` (`0x1b56f4`) -/
abbrev JA : Nat → Prop := JX impl R kc sqC mlC b L st pw pl lm x xl s 1791732 (fun _ _ => True) id
  (fun i => PV lm x xl s (i / 2) * PV lm x xl s (i / 2)) (2 * W lm) (sqC (ℓ1 (stLen s.mem st) pl lm) (W lm))

/-- after the first `trunc` (`0x1b5748`) -/
abbrev JB : Nat → Prop := JX impl R kc sqC mlC b L st pw pl lm x xl s 1791816 (fun i M => Lo2 s pw i M) id
  (fun i => PV lm x xl s i) (W lm) (sqC (ℓ1 (stLen s.mem st) pl lm) (W lm) + tC lm)

/-- after `mul` (`0x1b57cc`) -/
abbrev JC : Nat → Prop := JX impl R kc sqC mlC b L st pw pl lm x xl s 1791948 (fun i M => Lo2 s pw i M) (· + 1)
  (fun i => PV lm x xl s i * PV lm x xl s 1) (2 * W lm)
  (sqC (ℓ1 (stLen s.mem st) pl lm) (W lm) + tC lm + mlC (ℓ1 (stLen s.mem st) pl lm) (W lm) (W lm))

/-- after the second `trunc` (`0x1b5818`) -/
abbrev JD : Nat → Prop := JX impl R kc sqC mlC b L st pw pl lm x xl s 1792024 (fun i M => Lo2 s pw i M) (· + 1)
  (fun i => PV lm x xl s (i + 1)) (W lm) (rc sqC mlC (stLen s.mem st) pl lm)

end

end FvModexp.Arm64.P2Pre
