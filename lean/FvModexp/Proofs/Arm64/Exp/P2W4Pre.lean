import FvModexp.Proofs.Arm64.Exp.P2W4EnG3
import FvModexp.Proofs.Arm64.Exp.EvenHyp
import FvModexp.Proofs.Arm64.Exp.MulHyp

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the entry facts `EPre` (agent infra)

At the entry state `s` (`SP = sp + 752`, the function's frame will be `sp`), arguments `z = (zp, _, zc)` X0-2,
`stk = st` X3, `x = (xp, xl, xc)` X4-6, `y = (yp, yl, _)` X7-9, `logM = lm` X10. The window is `[sp - K, sp + 848)`
(`= [SP - (K + 752), SP + 96)`). Window-4 copy of `P2W2.EPre` (shape as agent expmc's window-2 `W2En.EPre` (same `OE` objects), plus the package
global `natOne` (read by `buildPrecomputationWindowModPower2`) and `st ≠ 0`). The stack bound `stLen + 2^13 ≤ 2^16`
covers `stk.nat(2w)` + the table's `stk.nat(17w)` (+ its `2^12` slack) + the loop's `sqr`/`mul`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 848) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the entry facts of `expNNPowerOfTwoWindowSize4` -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm : Nat) (s : State) : Prop :=
  EEnv R L g sp K s ∧ K ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 848)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧
  OE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ 0 < yl ∧ yl ≤ 2 ^ 12 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 2 ^ 12 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) RunIface.gA 32) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 848) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 848) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - K, sp + 848), (zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    EvenHyp.StkApart s.mem st op 8) ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array after the reserve: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

end FvModexp.Arm64.P2W4
