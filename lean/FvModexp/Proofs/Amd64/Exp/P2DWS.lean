import FvModexp.Proofs.Amd64.Exp.P2DDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the shape of the window summaries it calls (agent asm s67)

`expNNPowerOfTwo` calls `expNNPowerOfTwoWindowSize2` / `…Size4` (nat.go:960-966) for an odd base with `logM ≥ 2`, at
`RSP_S = RSP - 0x78` (window `[RSP_S - (stk - 0x78), RSP_S + 0x60)`: return address, `y` at `RSP_S + 8 … + 0x20`, the
spill area of the register arguments up to `RSP_S + 0x60`). divmc's amd64 P2W2 and top's P2W4 summaries are to be
stated as `WSum` (then they plug into `P2D.winCall` / `sumO` unchanged). s68: stack bound `kW ≤ stk ≤ 2^20`
and the `X15`/DF/`zp < 2^64` conjunct aligned with divmc's `P2W2.fullC` (bridge `P2D.wsum2`, P2DW2).
* `WPre`: `Regs` (`y` on the stack) ∧ (`X15 = 0`, DF clear, `zp < 2^64`) ∧ `NHyp.CPre` (inputs `x`, `y`, need `2^13`) ∧ `X > 0` odd ∧ `Y > 0` ∧
  `2 ≤ logM ≤ 2^13` ∧ `0 < st` ∧ the `natOne` facts ∧ `len x ≤ cap x < 2^40` ∧ the first three `NHyp.XGc` facts
  (= divmc's `P2W2.EX`) ∧ the return-address user-space bound.
* post: `PostD` (`RSP + 8`, `RBP`, `R14`, `X15` kept ∧ `NHyp.CPostR` with value `X^Y mod 2^logM`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- the precondition of a window summary (see the module doc) -/
@[reducible] def WPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat)
    (s : State) : Prop :=
  Regs s zp zl zc st xp xl xc yp yl yc lm ∧ (s.xmm 15 = 0 ∧ s.df = false ∧ zp < 2 ^ 64) ∧
    NHyp.CPre R b L stk A zp zl zc st [(xp, xl), (yp, yl)] (2 ^ 13) cst s ∧
    0 < natVal s.mem xp xl ∧ natVal s.mem xp xl % 2 = 1 ∧ 0 < natVal s.mem yp yl ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    (∃ op, EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      NHyp.StkApart s.mem st op 8) ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
    ((0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 ∧
      s.mem.accessible Callees.adxAddr 1 false = true) ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- **a window summary** at entry `e` (on `LibW`), stack need `kW`, budget `cW (len stk) (len y) logM` -/
def WSum (impl : List Amd64.Segment) (R : RtInv) (e kW : Nat) (cW : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (stk zp zl zc st xp xl xc yp yl yc lm : Nat), kW ≤ stk → stk ≤ 2 ^ 20 →
    Summary (LibW.program.link impl) e
      (fun s => WPre R b L stk 0x60 (cW (stLen s.mem st) yl lm) zp zl zc st xp xl xc yp yl yc lm s)
      (fun s s' => PostD R b L stk 0x60 (cW (stLen s.mem st) yl lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s')

end FvModexp.Amd64.P2D
