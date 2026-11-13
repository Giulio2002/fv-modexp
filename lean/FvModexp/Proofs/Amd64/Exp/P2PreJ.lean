import FvModexp.Proofs.Amd64.Exp.P2PreDefs
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): join statements and basic facts (agent divmc s61)

The function is a chain of segment lemmas over the entry state `s` (precondition `Pre`), each ending in the statement
of the next join as a hypothesis (segment modules independent, ROW-TIME LESSON):
* `JN` — the entry of `(*stack).nat` (`RSP_c = RSP - 184`, return `+0xb1`), after the frame set-up and the checks;
* `FillJ i` — the fill loop head `+0xd4` (nat.go:872).
Code map (offsets from `0x5e8900`): `stk.nat` call `+0xac`; fill store `+0xcd`, head `+0xd4`, write barrier `+0x14e`;
fill exit `+0x165`; `powers[0].set(natOne)` memmove `+0x268`, barrier `+0x2ae`; `trunc(x)` `+0x316`, barrier `+0x338`;
main loop head `+0x388`; `sqr` `+0x40e`, `trunc` `+0x460`, `mul` `+0x500`, `trunc` `+0x54f`; return `+0x5ab`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

/-- the entry of `(*stack).nat` -/
abbrev snE : Nat := 6186112

/-- the return address of the `stk.nat` call -/
abbrev snR : Nat := 0x5e8900 + 0xb1

/-- the fill loop's head -/
abbrev pcF : Nat := 0x5e8900 + 0xd4

/-- the frame state at a callee entry or a join: `RSP` (`RSP - 176` in the body, `- 184` at a callee entry),
`RBP = RSP - 8`, the ABI facts -/
@[reducible] def Frm (s S : State) (d : Nat) : Prop :=
  S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - d) ∧ S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧ Abi s S

/-- **JN**: at the `(*stack).nat` entry, `RAX = stk`, `RBX = (len+1) w`, return address `snR`; only the window written,
the frame slots `Sl` stored -/
def JN (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 snE → Frm s S 184 →
    S.mem.readLE ((s.regs 4).toNat - 184) 8 = snR →
    S.regs 0 = BitVec.ofNat 64 st → S.regs 3 = BitVec.ofNat 64 (NB pl lm) →
    MemFrame s.mem S.mem (win s (K kc) A) → S.mem.regions = s.mem.regions → Sl s st pw pl lm x xl S.mem →
    Goal impl R kc b L st pw pl lm x xl s S

/-- **FillJ i**: the fill loop head, `RAX = buf`, `RCX = cap buf = NB`, `RDX = powers`, `RSI = w`, `RBX = len`,
`RDI = i`; `powers[j]` for `j < i` filled -/
def FillJ (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 pcF → Frm s S 176 →
    S.regs 0 = BitVec.ofNat 64 bp → S.regs 1 = BitVec.ofNat 64 (NB pl lm) → S.regs 2 = BitVec.ofNat 64 pw →
    S.regs 6 = BitVec.ofNat 64 (W lm) → S.regs 3 = BitVec.ofNat 64 pl → S.regs 7 = BitVec.ofNat 64 i →
    Ctx R kc L st pw pl lm x xl s bp S.mem L1 b1 → (∀ j, j < i → PwT S.mem pw bp lm j) → i ≤ pl → b ≤ b1 →
    Goal impl R kc b L st pw pl lm x xl s S

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

theorem pl_facts (hpre : Pre R kc b L st pw pl ws lm x xl s) : 4 ≤ pl ∧ pl ≤ 16 ∧ pl % 2 = 0 := by
  obtain ⟨-, -, -, hws, hpl, -⟩ := hpre
  rcases hws with rfl | rfl <;> subst hpl <;> decide

theorem w_facts (hpre : Pre R kc b L st pw pl ws lm x xl s) : 1 ≤ W lm ∧ W lm ≤ 128 := by
  obtain ⟨-, -, -, -, -, h1, h2, -⟩ := hpre
  simp only [W]; omega

theorem nb_le {pl lm : Nat} (h1 : pl ≤ 16) (h2 : W lm ≤ 128) : NB pl lm ≤ 2176 := by
  simp only [NB]
  calc (pl + 1) * W lm ≤ 17 * 128 := Nat.mul_le_mul (by omega) h2
    _ = 2176 := rfl

theorem nb_pos {pl lm : Nat} (h1 : 1 ≤ pl) (h2 : 1 ≤ W lm) : 0 < NB pl lm := Nat.mul_pos (by omega) h2

end

end FvModexp.Amd64.P2Pre
