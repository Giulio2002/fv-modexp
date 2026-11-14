import FvModexp.Proofs.Amd64.Exp.P2PreLJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the main loop round's joins (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreJ` (`Lo`, `RS`, `JX`, `JA` … `JD`))

The round `i` (nat.go:891-897): `sqr` `+0x40e`, `trunc` `+0x460`, `mul` `+0x500`, `trunc` `+0x54f`; locals `i` at
`RSP - 56`, `3 i` at `RSP - 64` (written at `+0x3d7` / `+0x3e5`). `JX … pc kf v lb cst i`: the generic join at a callee
return `pc` inside round `i`, the result `(bp + 8 k w, l, 2 w)` (`RAX, RBX, RCX`; `k = kf i`) belongs to `powers[k]`:
value `v i`, `l ≤ lb`, budget spent `trunc(x)` + `i/2 - 1` rounds + `cst`. Unlike arm64 the round keeps no
`&powers[i+1]` slot (amd64 recomputes it from `3 i`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

/-- the round's locals: `i` at `RSP - 56`, `3 i` at `RSP - 64` -/
@[reducible] def Lo (s : State) (i : Nat) (M : Memory) : Prop :=
  M.readLE ((s.regs 4).toNat - 56) 8 = i ∧ M.readLE ((s.regs 4).toNat - 64) 8 = 3 * i

/-- the round facts at memory `M` while `powers[k]` is computed in round `i` -/
structure RS (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (X bp : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) (i k : Nat) : Prop where
  c : Ctx R kc L st pw pl lm x xl s bp M L1 b1
  d : ∀ j, j < k → PwD M pw bp lm X j
  t : ∀ j, k < j → j < pl → PwT M pw bp lm j
  lo : Lo s i M

/-- the generic join inside round `i`, after a call returning `powers[kf i]` -/
def JX (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) (pc : Nat) (kf v : Nat → Nat) (lb cst : Nat) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 l : Nat),
    Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 pc → Frm s S 176 →
    S.regs 0 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm)) → S.regs 3 = BitVec.ofNat 64 l →
    S.regs 1 = BitVec.ofNat 64 (2 * W lm) →
    RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp S.mem L1 b1 i (kf i) → l ≤ lb →
    natVal S.mem (bp + 8 * (kf i * W lm)) l = v i → NatNorm S.mem (bp + 8 * (kf i * W lm)) l →
    i % 2 = 0 → 2 ≤ i → i + 2 ≤ pl → b - (tC lm + (i / 2 - 1) * rc lm + cst) ≤ b1 →
    Goal impl R kc b L st pw pl lm x xl s S

section
variable (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State)

/-- after `sqr` (`+0x413`) -/
abbrev JA : Nat → Prop := JX impl R kc b L st pw pl ws lm x xl s (0x5e8900 + 0x413) id
  (fun i => PV lm x xl s (i / 2) * PV lm x xl s (i / 2)) (2 * W lm) (sqrCQ (W lm))

/-- after the first `trunc` (`+0x465`) -/
abbrev JB : Nat → Prop := JX impl R kc b L st pw pl ws lm x xl s (0x5e8900 + 0x465) id
  (fun i => PV lm x xl s i) (W lm) (sqrCQ (W lm) + tC lm)

/-- after `mul` (`+0x505`) -/
abbrev JC : Nat → Prop := JX impl R kc b L st pw pl ws lm x xl s (0x5e8900 + 0x505) (· + 1)
  (fun i => PV lm x xl s i * PV lm x xl s 1) (2 * W lm) (sqrCQ (W lm) + tC lm + mulCQ (W lm) (W lm))

/-- after the second `trunc` (`+0x554`) -/
abbrev JD : Nat → Prop := JX impl R kc b L st pw pl ws lm x xl s (0x5e8900 + 0x554) (· + 1)
  (fun i => PV lm x xl s (i + 1)) (W lm) (rc lm)

end

end FvModexp.Amd64.P2Pre
