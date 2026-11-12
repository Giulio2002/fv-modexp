import FvModexp.Proofs.Arm64.Exp.LibN
import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Arm64.Exp.MulHyp
import FvModexp.Proofs.Arm64.Exp.OddDefs

/-!
# `nat.expNN` (arm64), stack given (`stk ≠ nil`), modulus odd or a power of two: statement layer

`z.expNN(stk, x, y, m, slow)` (nat.go:639-722), `fn = 0x1b42b0`, frame 256 (`SP' = SP - 256`, saved FP/LR at `SP' - 8`,
`SP'`), argument spills to the caller's area `SP + 8 .. SP + 113` (`z` at 264(RSP'), `x` 296.., `y` 320.., `m` 344..,
`slow` byte 368). The callee frames: `expNNOdd` enters with `SP'` (its `sp = SP' - 1056 = SP - 1312`), `rem` /
`expNNSlow` / `expNNPowerOfTwo` enter with `SP'` (window `[SP' - stk, SP' + 112)`).

Here `sp := SP - 1312` (= `expNNOdd`'s `sp`) and the window is `[sp - K, sp + 1432) = [SP - (K + 1312), SP + 120)`.

* `NPre`: as `ExpOdd.OPre` with the larger window, `0 < st` (stack given), `slow = 0`, `0 < len m`, `len z ≤ cap z`,
  the package global `natOne` (read by `expNNPowerOfTwo`'s precomputation), the alias condition
  of `z` (Go `alias(z, x) || alias(z, y)` → `z = nil`; otherwise `z` is apart from `x`, `y`, `m`: `ZOK`), the stack
  bounds of every callee, the budget `NBud`.
* `Pre` = `NPre` ∧ (`M` odd ∨ `M` a power of two) (`noEven`: `expNNEven` is never called).
* `Post`: `X0..X2 = (p, l, c)` with value `X ^ Y % M`, normalised, `c = 0` or `z`'s array or a fresh one, `LiveExt`,
  budget `NCost`, `StackBackL`, frame `R.rt ++ winA s (K + 1312) 120 ++ [z] ++ stkWs`, `LiveFrame`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN"

/-- the function's names (`LibN`: `LibOdd` and `nat.expNN`) -/
abbrev names : List String := LibN.names

/-- entry (`0x1b42b0`) -/
abbrev fnN : Nat := 1786544

/-- an operand at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def NE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 1432) ∧ Apart a k st 24 ∧
    Apart a k (W4En.free M st).1 (W4En.free M st).2

/-- the call environment at the entry (`SP = sp + 1312`) -/
@[reducible] def NEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (s : State) : Prop :=
  s.sp = BitVec.ofNat 64 (sp + 1312) ∧ s.regs 28 = BitVec.ofNat 64 g ∧
  g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧
  Outside (g + 16) 8 ((sp - K, sp + 1432) :: R.rt) ∧ sp % 16 = 0 ∧ 4304 ≤ K ∧ K ≤ sp ∧ sp + 1432 ≤ 2 ^ 48 ∧
  s.mem.accessible (sp - K) (K + 1432) true = true ∧ LiveSep [(sp - K, sp + 1432)] R.rt ∧
  LiveSep L [(sp - K, sp + 1432)] ∧ Extracted.program.DataLoaded s.mem ∧ RunIface.Serves R

/-- `z` kept by the alias test: writable, held, apart from the window, the guard word, the stack, the operands and the
threshold globals -/
@[reducible] def ZOK (R : RtInv) (L : List (Nat × Nat)) (g sp K st zp zc xp xl yp yl mp n : Nat) (M : Memory) : Prop :=
  NE R L sp K st M zp (8 * zc) ∧ M.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧
    NatLive M R L zp zc ∧ Apart (g + 16) 8 zp (8 * zc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
    Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) RunIface.gA 32

/-- the precondition's facts (entry state `s`, `sp = SP - 1312`, stack-size and cost parameters of the callees) -/
def NPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (g sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NEnv R L g sp K s ∧ K + 288 ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 1432)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧ slow = 0 ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  NE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  NE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ yl ≤ 2 ^ 9 ∧ yc < 2 ^ 64 ∧
  NE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zl ≤ zc ∧ zc < 2 ^ 40 ∧
  (0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨
    ZOK R L g sp K st zp zc xp xl yp yl mp n s.mem) ∧
  NE R L sp K st s.mem RunIface.gA 32 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - K, sp + 1432), (zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    EvenHyp.StkApart s.mem st op 8) ∧
  0 < st ∧ st < 2 ^ 48 ∧ StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 1432) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 1432) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (W4En.free s.mem st).1 (W4En.free s.mem st).2 ∧
  Apart (W4En.free s.mem st).1 (W4En.free s.mem st).2 RunIface.gA 32 ∧
  stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧
  stLen s.mem st + needR xl n ≤ 2 ^ 16 ∧ stLen s.mem st + needS xl yl n ≤ 2 ^ 16 ∧
  stLen s.mem st + needP xl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16 ∧
  makeCost 1 + makeCost n + costR (stLen s.mem st) xl n + costS (stLen s.mem st) xl yl n +
    costP (stLen s.mem st) xl yl (Nat.log2 (natVal s.mem mp n)) + ExpOdd.OBud costF n xl yl (stLen s.mem st) ≤ b ∧
  R.inv b L g (view R.rt L s.mem)

/-- the cost the postcondition charges (an upper bound of every path's) -/
def NCost (costF : Nat → Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (xl yl n l lm : Nat) : Nat :=
  makeCost 1 + makeCost n + costR l xl n + costS l xl yl n + costP l xl yl lm + ExpOdd.OCost costF n xl yl l

/-- the precondition (entry state `s`; arguments `[z, zl, zc, st, x, xl, xc, y, yl, yc, m, n, mc, slow]`) -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NPre R b L K costF needR costR needS needP costS costP (s.regs 28).toNat (s.sp.toNat - 1312) zp zl zc st xp xl xc yp
    yl yc mp n mc slow s ∧
  (natVal s.mem mp n % 2 = 1 ∨ ∃ k, natVal s.mem mp n = 2 ^ k)

/-- the postcondition (results `X0..X2`): `x^y mod m`, normalised, empty, in `z`'s array or in a fresh one -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zc st xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ c < 2 ^ 64 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - NCost costF costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      (c = 0 ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 1312) 120 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ ResSep s.mem s'.mem st p c

end FvModexp.Arm64.ExpN
