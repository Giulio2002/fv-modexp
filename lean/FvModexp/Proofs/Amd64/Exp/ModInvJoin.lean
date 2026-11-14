import FvModexp.Proofs.Amd64.Exp.ModInvRnd
import FvModexp.Proofs.Common.ModInvRound

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the joins inside a Hensel round (agent infra s56; twin of
`Arm64/Exp/ModInvJoin`, definitions only — every round segment module imports this one directly)

A round (`i = 2^j`; loop body nat.go:1327-1332 at `+0x382 … +0x4ef`, final round nat.go:1334-1339 at
`+0x510 … +0x605`) is six calls on `z = (p, l, c)` (value `Zv`, `X · Zv ≡ 1 (mod 2^(2^j·32))`) and
`zz = (q, ql, qc)`: `zz = zz.sqr(stk, z)` → `S1` → `zz = zz.trunc(zz, e)` → `S2` → `zz = zz.mul(stk, zz, x[:k])` →
`S3` → `zz = zz.trunc(zz, e)` → `S4` → (`zz` stored) `z = z.lsh(z, 1)` → `S5` → `z = z.subMod2N(z, zz, e)` (then the
loop head `J2` at `j + 1`, or the return). Loop: `e = i·64`, `k = min(i, len x)`; final round: `e = n`,
`k = min(numWords, len x)`. Each join `Sk pcv Ex E Kx` is stated once for both (`pcv` the return address, `Ex j M`
the stage's slot / loop facts, `E j` the `trunc` width, `Kx j` the `x` prefix length). Results come back in
`RAX, RBX, RCX`; the frame `RSP' = RSP - 224` holds `z` at `0xd0 / 0xb0 / 0xb8(SP')` (`RSP - 16 / - 48 / - 40`),
`zz` at `0xc8 / 0x68 / 0x70(SP')` (`RSP - 24 / - 120 / - 112`), `i` at `0x98(SP')` (`RSP - 72`), `i·64` at
`0xa8(SP')` (`RSP - 56`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

/-- a fact hidden from `janus64_run` (which destructures every conjunction in context) -/
structure Box (P : Prop) : Prop where
  h : P

/-- the round's budget pieces, in call order (round `j`, `x` prefix `k`) -/
@[reducible] def P1 (sqrC : Nat → Nat) (n j : Nat) : Nat := sqrC (zB n j)
@[reducible] def P2 (sqrC : Nat → Nat) (n j : Nat) : Nat := P1 sqrC n j + makeCost (2 * NW n + 2)
@[reducible] def P3 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j k : Nat) : Nat :=
  P2 sqrC n j + mulC k (min k xl)
@[reducible] def P4 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j k : Nat) : Nat :=
  P3 sqrC mulC xl n j k + makeCost (2 * NW n + 2)
@[reducible] def P5 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j k : Nat) : Nat :=
  P4 sqrC mulC xl n j k + makeCost (NW n + 2)

/-- `z`'s slots (`RSP - 16 / - 48 / - 40`) -/
@[reducible] def ZS (s : State) (M : Memory) (p l c : Nat) : Prop :=
  M.readLE ((s.regs 4).toNat - 16) 8 = p ∧ M.readLE ((s.regs 4).toNat - 48) 8 = l ∧
    M.readLE ((s.regs 4).toNat - 40) 8 = c

/-- `zz`'s slots (`RSP - 24 / - 120 / - 112`) -/
@[reducible] def QS (s : State) (M : Memory) (q ql qc : Nat) : Prop :=
  M.readLE ((s.regs 4).toNat - 24) 8 = q ∧ M.readLE ((s.regs 4).toNat - 120) 8 = ql ∧
    M.readLE ((s.regs 4).toNat - 112) 8 = qc

/-- the facts at every join of round `j` (state `S`, live set `L1`, budget `b1`, `z = (p, l, c)`, `zz = (q, ql, qc)`,
`Zv` the value of `z` at the round's start) -/
@[reducible] def RC (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (Kx : Nat → Nat) (s S : State) (j : Nat)
    (L1 : List (Nat × Nat)) (b1 p l c q ql qc Zv : Nat) : Prop :=
  Box (Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) ∧ 64 < n ∧
    S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) ∧ S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧
    Abi s S ∧ Box (Mid R kc L s zp zc st xp xl xc n S.mem L1 b1 p l c q ql qc) ∧
    1 ≤ j ∧ 2 ^ (j - 1) < NW n ∧ spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (Kx j) ≤ b ∧
    natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)

/-- after `zz = zz.sqr(stk, z)` -/
def S1 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (_E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc H sqrC mulC b L zp zl zc st xp xl xc n Kx s S j L1 b1 p l c q ql qc Zv →
    S.rip = BitVec.ofNat 64 pcv → Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ zB n j →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 3 = BitVec.ofNat 64 ql → S.regs 1 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv → NatNorm S.mem q ql → ql ≤ 2 * NW n + 2 →
    b - spent sqrC mulC xl n j - P1 sqrC n j + stkR H S.mem st ≤ b1 →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- after the first `zz = zz.trunc(zz, e)` -/
def S2 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc H sqrC mulC b L zp zl zc st xp xl xc n Kx s S j L1 b1 p l c q ql qc Zv →
    S.rip = BitVec.ofNat 64 pcv → Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ zB n j →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 3 = BitVec.ofNat 64 ql → S.regs 1 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j → NatNorm S.mem q ql → ql ≤ NW n → ql ≤ Kx j →
    b - spent sqrC mulC xl n j - P2 sqrC n j + stkR H S.mem st ≤ b1 →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- after `zz = zz.mul(stk, zz, x[:k])` -/
def S3 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc H sqrC mulC b L zp zl zc st xp xl xc n Kx s S j L1 b1 p l c q ql qc Zv →
    S.rip = BitVec.ofNat 64 pcv → Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ zB n j →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 3 = BitVec.ofNat 64 ql → S.regs 1 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) → NatNorm S.mem q ql →
    ql ≤ 2 * NW n →
    b - spent sqrC mulC xl n j - P3 sqrC mulC xl n j (Kx j) + stkR H S.mem st ≤ b1 →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- after the second `zz = zz.trunc(zz, e)` -/
def S4 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc H sqrC mulC b L zp zl zc st xp xl xc n Kx s S j L1 b1 p l c q ql qc Zv →
    S.rip = BitVec.ofNat 64 pcv → Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ zB n j →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 3 = BitVec.ofNat 64 ql → S.regs 1 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j → NatNorm S.mem q ql →
    ql ≤ NW n →
    b - spent sqrC mulC xl n j - P4 sqrC mulC xl n j (Kx j) + stkR H S.mem st ≤ b1 →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- after `z = z.lsh(z, 1)` (`zz` in its slots, the new `z` in `RAX, RBX, RCX`) -/
def S5 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc H sqrC mulC b L zp zl zc st xp xl xc n Kx s S j L1 b1 p l c q ql qc Zv →
    S.rip = BitVec.ofNat 64 pcv → Ex j S.mem → QS s S.mem q ql qc →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 3 = BitVec.ofNat 64 l → S.regs 1 = BitVec.ofNat 64 c →
    natVal S.mem p l = Zv * 2 → NatNorm S.mem p l → l ≤ NW n + 2 →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j → NatNorm S.mem q ql →
    ql ≤ NW n →
    b - spent sqrC mulC xl n j - P5 sqrC mulC xl n j (Kx j) + stkR H S.mem st ≤ b1 →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-! ## The loop round's and the final round's instances -/

/-- loop: `E j = 2^j·64` -/
@[reducible] def eL (j : Nat) : Nat := 2 ^ j * 64
/-- loop: `Kx j = 2^j` -/
@[reducible] def kL (j : Nat) : Nat := 2 ^ j

/-- loop round `J`: `i = 2^j < numWords` and `j = J` (fixes the round, for the induction over rounds) -/
@[reducible] def LJ (n J j : Nat) : Prop := 2 ^ j < NW n ∧ j = J

/-- loop stage facts: `i` (or `2i`, stored before the `mul` call) at `RSP - 72`, `i·64` at `RSP - 56`, round `J` -/
@[reducible] def ExL1 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ j ∧ LJ n J j
@[reducible] def ExL2 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ j ∧ M.readLE ((s.regs 4).toNat - 56) 8 = 2 ^ j * 64 ∧ LJ n J j
@[reducible] def ExL3 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ (j + 1) ∧ M.readLE ((s.regs 4).toNat - 56) 8 = 2 ^ j * 64 ∧ LJ n J j

/-- final round: `E = n`, `Kx = numWords`, `numWords ≤ i` -/
@[reducible] def ExF (n j : Nat) (_M : Memory) : Prop := NW n ≤ 2 ^ j
@[reducible] def eF (n _j : Nat) : Nat := n
@[reducible] def kF (n _j : Nat) : Nat := NW n

end FvModexp.Amd64.ModInv
