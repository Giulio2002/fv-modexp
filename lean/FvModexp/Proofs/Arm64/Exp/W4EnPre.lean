import FvModexp.Proofs.Arm64.Exp.W4EnG
import FvModexp.Proofs.Arm64.Exp.W4Fin

/-!
# window-4 entry (arm64): the entry facts `EPre` of `nat.expNNOddMontgomeryWindowSize4`

At the entry state `s` (`SP = sp + 928`, the function's frame will be `sp`), arguments `z = (zp, _, zc)` X0-2,
`stk = st` X3, `x = (xp, xl, xc)` X4-6, `y = (yp, ylen, _)` X7-9, `m = (mp, n, mc)` X10-12. The window is
`[sp - K, sp + 1040)` (`= [SP - (K + 928), SP + 112)`); `l0 = len + rnd(23n)` is the stack level after the inline
`stk.reserve(23n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an operand object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 1040) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the entry facts of window-4 (budget closure: `xb` is any bound of the x-normalisation/`RR`/table/`z` costs that
`W4Pro.xnStep` needs, see `EBud`) -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (g sp st zp zc xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EEnv R L g sp K s ∧ K ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 1040)] ∧ RoOut R ∧ Outside StackNat.wT 16 R.rt ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  OE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  OE R L sp K st s.mem yp (8 * ylen) ∧ s.mem.accessible yp (8 * ylen) false = true ∧ yp + 8 * ylen ≤ 2 ^ 48 ∧
    NatNorm s.mem yp ylen ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ 0 < xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (2 * n ≤ zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 1040) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 1040) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  R.inv b L g (view R.rt L s.mem)

end FvModexp.Arm64.W4En
