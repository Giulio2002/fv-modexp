import FvModexp.Proofs.Amd64.Exp.P2W2Defs
import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the entry facts `EPre` (agent divmc s66; amd64 twin of `Arm64.P2W2.EPre`,
window shape of agent expmc's amd64 `W2En.EPre`)

At the entry state `s` (`RSP = sp + 0x1d0`, the function's frame is `sp`), register arguments `z = (zp, _, zc)`
`AX, BX, CX`, `stk = st` `DI`, `x = (xp, xl, xc)` `SI, R8, R9`, `logM = lm` `R10`; the stack argument
`y = (yp, yl, _)` at `sp + 0x1d8`. The window is `[sp - 8 - K, sp + 0x230)` (callee stacks, frame, saved `BP`, return
address, `y`, register spill area). As on arm64: the package global `natOne` (read by
`buildPrecomputationWindowModPower2`), `st ≠ 0`, the stack bound `stLen + 2^13 ≤ 2^16` and the budget with the
stack-reserve potential `stkR (HW ℓ₀ lm)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - 8 - K) (K + 0x238) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the stack reserve level of the function for an entry stack length `ℓ0` (as `Arm64.P2W2.HW`): the reserve `8 w`,
`zz` (`rnd 2w`), then `buildPrecomputationWindowModPower2`'s span (`rnd 5w + 8 w + 64`) -/
@[reducible] def HW (l0 lm : Nat) : Nat :=
  l0 + 8 * W lm + StackNat.rnd (2 * W lm) + (StackNat.rnd (5 * W lm) + 8 * W lm + 64)

/-- the entry facts of `expNNPowerOfTwoWindowSize2` -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) : Prop :=
  EEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - 8 - K, sp + 0x230)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧
  OE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ 0 < yl ∧ yl ≤ 2 ^ 12 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 2 ^ 12 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧
    Apart zp (8 * zc) RunIface.gA 32) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x238) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x238) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 ∧
  (s.regs 5).toNat = bp ∧ s.mem.readLE (sp + 0x1d0) 8 = r ∧ r < 2 ^ 47 ∧
  s.mem.readLE (sp + 0x1d8) 8 = yp ∧ s.mem.readLE (sp + 0x1e0) 8 = yl ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - 8 - K, sp + 0x230), (zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    NHyp.StkApart s.mem st op 8) ∧
  R.inv (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g (view R.rt L s.mem)

/-- the array after the reserve: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

end FvModexp.Amd64.P2W2
