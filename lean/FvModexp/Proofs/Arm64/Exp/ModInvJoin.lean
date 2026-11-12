import FvModexp.Proofs.Arm64.Exp.ModInvBuild
import FvModexp.Proofs.Arm64.Exp.ModInvBuild2
import FvModexp.Proofs.Common.ModInvRound

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the joins inside a Hensel round (agent infra)

A round (`i = 2^j`; loop body nat.go:1327-1332, final round nat.go:1334-1339) is six calls on `z = (p, l, c)` (value
`Zv`, `X · Zv ≡ 1 (mod 2^(2^j·32))`) and `zz = (q, ql, qc)`:
`zz = zz.sqr(stk, z)` → `S1` → `zz = zz.trunc(zz, e)` → `S2` → `zz = zz.mul(stk, zz, x[:k])` → `S3` →
`zz = zz.trunc(zz, e)` → `S4` → `z = z.lsh(z, 1)` → `S5` → `z = z.subMod2N(z, zz, e)` (then the loop head `J2` at
`j + 1`, or the return). Loop: `e = i·64`, `k = min(i, len x)`; final round: `e = n`, `k = min(numWords, len x)`.
Each join `Sk pcv Ex E Kx` is stated once for both (`pcv` the return address, `Ex j M` the stage's slot / loop facts,
`E j` the `trunc` width, `Kx j` the `x` prefix length); one module per call segment proves `Sk` from `S(k+1)`.
Budget: the round's pieces (`P1 … P5`, then `subMod2N`'s) are spent in order.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- a fact hidden from `janus_run` (which destructures every conjunction in context) -/
structure Box (P : Prop) : Prop where
  h : P

/-- the round's budget pieces, in call order -/
@[reducible] def P1 (sqrC : Nat → Nat) (n : Nat) : Nat := sqrC (NW n + 1)
@[reducible] def P2 (sqrC : Nat → Nat) (n : Nat) : Nat := P1 sqrC n + makeCost (2 * NW n + 2)
@[reducible] def P3 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (n : Nat) : Nat :=
  P2 sqrC n + mulC (2 * NW n + 2) (NW n)
@[reducible] def P4 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (n : Nat) : Nat :=
  P3 sqrC mulC n + makeCost (2 * NW n + 2)
@[reducible] def P5 (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (n : Nat) : Nat :=
  P4 sqrC mulC n + makeCost (NW n + 2)

/-- `z`'s slots (`SP - 16 / - 48 / - 56`) -/
@[reducible] def ZS (s : State) (M : Memory) (p l c : Nat) : Prop :=
  M.readLE (s.sp.toNat - 16) 8 = p ∧ M.readLE (s.sp.toNat - 48) 8 = l ∧ M.readLE (s.sp.toNat - 56) 8 = c

/-- `zz`'s slots (`SP - 24 / - 128 / - 120`) -/
@[reducible] def QS (s : State) (M : Memory) (q ql qc : Nat) : Prop :=
  M.readLE (s.sp.toNat - 24) 8 = q ∧ M.readLE (s.sp.toNat - 128) 8 = ql ∧ M.readLE (s.sp.toNat - 120) 8 = qc

/-- the facts at every join of round `j` (state `S`, live set `L1`, budget `b1`, `z = (p, l, c)`, `zz = (q, ql, qc)`,
`Zv` the value of `z` at the round's start) -/
@[reducible] def RC (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s S : State) (j : Nat) (L1 : List (Nat × Nat))
    (b1 p l c q ql qc Zv : Nat) : Prop :=
  Box (Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) ∧ 64 < n ∧
    S.sp = BitVec.ofNat 64 (s.sp.toNat - 240) ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18 ∧
    Box (Mid R kc L s zp zc st xp xl xc n S.mem L1 b1 p l c q ql qc) ∧
    1 ≤ j ∧ 2 ^ (j - 1) < NW n ∧ spent sqrC mulC n j + roundCost sqrC mulC n ≤ b ∧
    natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)

/-- after `zz = zz.sqr(stk, z)` -/
def S1 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc sqrC mulC b L zp zl zc st xp xl xc n s S j L1 b1 p l c q ql qc Zv → S.pc = BitVec.ofNat 64 pcv →
    Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ NW n + 1 →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 1 = BitVec.ofNat 64 ql → S.regs 2 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv → NatNorm S.mem q ql → ql ≤ 2 * NW n + 2 →
    b - spent sqrC mulC n j - P1 sqrC n ≤ b1 →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-- after the first `zz = zz.trunc(zz, e)` -/
def S2 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc sqrC mulC b L zp zl zc st xp xl xc n s S j L1 b1 p l c q ql qc Zv → S.pc = BitVec.ofNat 64 pcv →
    Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ NW n + 1 →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 1 = BitVec.ofNat 64 ql → S.regs 2 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j → NatNorm S.mem q ql → ql ≤ NW n →
    b - spent sqrC mulC n j - P2 sqrC n ≤ b1 →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-- after `zz = zz.mul(stk, zz, x[:k])` -/
def S3 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc sqrC mulC b L zp zl zc st xp xl xc n s S j L1 b1 p l c q ql qc Zv → S.pc = BitVec.ofNat 64 pcv →
    Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ NW n + 1 →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 1 = BitVec.ofNat 64 ql → S.regs 2 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) → NatNorm S.mem q ql →
    ql ≤ 2 * NW n →
    b - spent sqrC mulC n j - P3 sqrC mulC n ≤ b1 →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-- after the second `zz = zz.trunc(zz, e)` -/
def S4 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc sqrC mulC b L zp zl zc st xp xl xc n s S j L1 b1 p l c q ql qc Zv → S.pc = BitVec.ofNat 64 pcv →
    Ex j S.mem → ZS s S.mem p l c → natVal S.mem p l = Zv → 0 < l → l ≤ NW n + 1 →
    S.regs 0 = BitVec.ofNat 64 q → S.regs 1 = BitVec.ofNat 64 ql → S.regs 2 = BitVec.ofNat 64 qc →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j → NatNorm S.mem q ql →
    ql ≤ NW n →
    b - spent sqrC mulC n j - P4 sqrC mulC n ≤ b1 →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-- after `z = z.lsh(z, 1)` (`zz` in its slots, the new `z` in `X0 … X2`) -/
def S5 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) (pcv : Nat) (Ex : Nat → Memory → Prop)
    (E Kx : Nat → Nat) : Prop :=
  ∀ (S : State) (j p l c q ql qc : Nat) (L1 : List (Nat × Nat)) (b1 Zv : Nat),
    RC R kc sqrC mulC b L zp zl zc st xp xl xc n s S j L1 b1 p l c q ql qc Zv → S.pc = BitVec.ofNat 64 pcv →
    Ex j S.mem → QS s S.mem q ql qc →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 l → S.regs 2 = BitVec.ofNat 64 c →
    natVal S.mem p l = Zv * 2 → NatNorm S.mem p l → l ≤ NW n + 2 →
    natVal S.mem q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j → NatNorm S.mem q ql →
    ql ≤ NW n →
    b - spent sqrC mulC n j - P5 sqrC mulC n ≤ b1 →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-! ## The loop round's and the final round's instances -/

/-- loop: `E j = 2^j·64` -/
@[reducible] def eL (j : Nat) : Nat := 2 ^ j * 64
/-- loop: `Kx j = 2^j` -/
@[reducible] def kL (j : Nat) : Nat := 2 ^ j

/-- loop round `J`: `i = 2^j < numWords` and `j = J` (fixes the round, for the induction over rounds) -/
@[reducible] def LJ (n J j : Nat) : Prop := 2 ^ j < NW n ∧ j = J

/-- loop stage facts: `i` (or `2i`) at `SP - 80`, `i·64` at `SP - 64`, round `J` -/
@[reducible] def ExL1 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 80) 8 = 2 ^ j ∧ LJ n J j
@[reducible] def ExL2 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 80) 8 = 2 ^ j ∧ M.readLE (s.sp.toNat - 64) 8 = 2 ^ j * 64 ∧ LJ n J j
@[reducible] def ExL3 (s : State) (n J j : Nat) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 80) 8 = 2 ^ (j + 1) ∧ M.readLE (s.sp.toNat - 64) 8 = 2 ^ j * 64 ∧ LJ n J j

/-- final round: `E = n`, `Kx = numWords`, `numWords ≤ i` -/
@[reducible] def ExF (n j : Nat) (_M : Memory) : Prop := NW n ≤ 2 ^ j

end FvModexp.Arm64.ModInv
