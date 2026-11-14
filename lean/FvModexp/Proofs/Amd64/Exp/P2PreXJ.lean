import FvModexp.Proofs.Amd64.Exp.P2PreJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the join after `powers[0].set(natOne)` (agent divmc s63; twin of
infra's `Arm64/Exp/P2PreX`'s `X1J`)

`X1J`: the pointer store `powers[0].ptr = buf` `+0x2ba` (both write-barrier branches join there), `RDX = powers`,
`RBX = len`, `RSI = w`, `R10 = 2 w`, `R12 = buf`, `RCX = 1`; `powers[j]` for `1 ≤ j < len` as the fill loop left them,
`buf[0] = 1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

/-- the pointer store of `powers[0]` -/
abbrev pcX1 : Nat := 0x5e8900 + 0x2ba

/-- **X1J**: the pointer store of `powers[0] = powers[0].set(natOne)` -/
def X1J (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 pcX1 → Frm s S 176 →
    S.regs 2 = BitVec.ofNat 64 pw → S.regs 3 = BitVec.ofNat 64 pl → S.regs 6 = BitVec.ofNat 64 (W lm) →
    S.regs 10 = BitVec.ofNat 64 (2 * W lm) → S.regs 12 = BitVec.ofNat 64 bp → S.regs 1 = BitVec.ofNat 64 1 →
    Ctx R kc L st pw pl lm x xl s bp S.mem L1 b1 → (∀ j, 1 ≤ j → j < pl → PwT S.mem pw bp lm j) →
    S.mem.readLE bp 8 = 1 → b ≤ b1 →
    Goal impl R kc b L st pw pl lm x xl s S

end FvModexp.Amd64.P2Pre
