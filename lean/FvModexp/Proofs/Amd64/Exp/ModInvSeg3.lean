import FvModexp.Proofs.Amd64.Exp.ModInvRt
import FvModexp.Proofs.Common.ModInvRound

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the Hensel loop head `J2` (agent infra s55; twin of `Arm64/Exp/ModInvSeg3`)

`J2` (`+0x4ef` = `0x5eadaf`, nat.go:1325 `i < numWords` test, before the stores of `z` to `0xb8/0xb0/0xd0(SP')`):
`R12 = i = 2^j`, `z = (RAX, RDX, RCX)` (`p, l, c`), `zz = (R15, R13, R11)` (`q, ql, qc`), `RBX = numWords`,
`RDI = stk`, `RSI, R8, R9 = x`, `R10 = n`. Invariant: `X · Z ≡ 1 (mod 2^(2^j · 32))` (`Exp.round_inv`; at `j = 1`
from `Z mod 2^64 = k0`), both arrays owned (caller's `z` or fresh), apart; `cap z ≥ numWords + 1`; budget after the
two `make`s and `j - 1` rounds.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

/-- the return address, the saved `RBP` and the spills the loop reloads (`stk`, `x`, `n`, `numWords`) -/
@[reducible] def Fw2 (s : State) (M : Memory) (st xp xl xc n : Nat) : Prop :=
  Fw0 s M ∧ M.readLE ((s.regs 4).toNat + 32) 8 = st ∧ M.readLE ((s.regs 4).toNat + 40) 8 = xp ∧
    M.readLE ((s.regs 4).toNat + 48) 8 = xl ∧ M.readLE ((s.regs 4).toNat + 56) 8 = xc ∧
    M.readLE ((s.regs 4).toNat + 64) 8 = n ∧ M.readLE ((s.regs 4).toNat - 104) 8 = NW n

theorem Fw1.toFw2 {s : State} {M : Memory} {st xp xl xc n k : Nat} (h : Fw1 s M st xp xl xc n k) :
    Fw2 s M st xp xl xc n :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- the budget spent before round `j` -/
@[reducible] def spent (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j : Nat) : Nat :=
  makeCost (NW n + 1) + makeCost (2 * NW n) + sumR sqrC mulC xl n (j - 1)

/-- **J2** at round `j`: the loop head (see the module doc) -/
def J2j (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (j : Nat) : Prop :=
  ∀ (S : State) (p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x4ef) → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) →
    S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) → Abi s S →
    S.regs 12 = BitVec.ofNat 64 (2 ^ j) → S.regs 0 = BitVec.ofNat 64 p → S.regs 2 = BitVec.ofNat 64 l →
    S.regs 1 = BitVec.ofNat 64 c → S.regs 15 = BitVec.ofNat 64 q → S.regs 13 = BitVec.ofNat 64 ql →
    S.regs 11 = BitVec.ofNat 64 qc → S.regs 3 = BitVec.ofNat 64 (NW n) →
    S.regs 7 = BitVec.ofNat 64 st → S.regs 6 = BitVec.ofNat 64 xp → S.regs 8 = BitVec.ofNat 64 xl →
    S.regs 9 = BitVec.ofNat 64 xc → S.regs 10 = BitVec.ofNat 64 n →
    Fw2 s S.mem st xp xl xc n → RtM R kc L s zp zc st S.mem L1 b1 → b - spent sqrC mulC xl n j + stkR H S.mem st ≤ b1 →
    Own R kc L L1 s zp zc st xp xl S.mem p c → Own R kc L L1 s zp zc st xp xl S.mem q qc →
    NW n + 1 ≤ c → l ≤ zB n j → l ≤ c → ql ≤ qc → 0 < qc → 1 ≤ j → 2 ^ (j - 1) < NW n →
    Apart p (8 * c) q (8 * qc) →
    natVal s.mem xp xl * natVal S.mem p l % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32) →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- **J2**: the loop head at every round -/
def J2 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ j, J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s j

end FvModexp.Amd64.ModInv
