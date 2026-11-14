import FvModexp.Proofs.Amd64.Exp.LibN
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.OddDefs

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), stack given (`stk ≠ nil`), modulus odd or a power of two: statement layer (agent expmc s66;
twin of `Arm64.ExpN` NDefs)

`z.expNN(stk, x, y, m, slow)` (nat.go:639-722), `fn = 0x5e6fa0`. Arguments (ABIInternal, `dis/nat.expNN.amd64.s`):
`z` RAX,RBX,RCX, `stk` RDI, `x` RSI,R8,R9, `slow` R10 (byte); `y` at `E + 8 … E + 0x18`, `m` at `E + 0x20 … E + 0x30`
(`E` = the entry `RSP`). Stack check `LEAQ -0x88(SP), R12; CMPQ R12, 0x10(R14); JBE`, `PUSHQ BP`, `SUBQ $0x100, SP`
(`SP' = E - 0x108`), spills `AX → E + 0x38`, `SI → E + 0x58`, `R8 → E + 0x60`, `R9 → E + 0x68`, `R10 → E + 0x70` (the
caller's area ends at `E + 0x78`). Every callee is entered with `RSP = E - 0x110`; `expNNOdd`'s `sp` (`RSP - 0x388`) is
`E - 0x498`.

Here `sp := E - 0x498` (= `expNNOdd`'s `sp`) and the window is `[sp - K, sp + 0x510) = [E - (K + 0x498), E + 0x78)`;
`expNNOdd` runs with `K - 8` (its window `[sp - 8 - (K - 8), sp + 0x3f8)`).

* `NPre`: the entry facts (`NEnv`: `CallW.CEnv` on the window, `R14 = g`, `FS` base, `X15 = 0`, `DF` clear), the operands
  (`x` with its capacity: `expNNOdd` reads `x` up to `cap`), `0 < st` (stack given), `slow = 0`, `0 < len m`, the
  alias condition of `z` (`ZOK`), the package global `natOne` (`expNNPowerOfTwo`), the stack bounds of every callee, the
  budget (PATH MAX of the branches' costs; `expNNOdd`'s closed budget `ExpOdd.OBud` at `b - makeCost n`).
* `Pre` = `NPre` at `sp = RSP - 0x498` ∧ (`M` odd ∨ `M` a power of two) ∧ `NHyp.XFacts`.
* `Post`: `FS` base and `DF` kept, `RAX, RBX, RCX = (p, l, c)` with value `X ^ Y % M`, normalised, `c = 0` or `z`'s
  array or a fresh one, `LiveExt`, budget `NCost`, `StackBackL`, frame `R.rt ++ win s (K + 0x498) 0x78 ++ [z] ++
  stkWs`, `LiveFrame`, `ResSep`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN"

/-- the function's names (`LibN`: `LibOdd`, the callees and `nat.expNN`) -/
abbrev names : List String := LibN.names

/-- entry (`0x5e6fa0`) -/
abbrev fnN : Nat := 6188960

/-- an operand at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def NE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Janus.Arm64.Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 0x510) ∧ Apart a k st 24 ∧
    Apart a k (W4En.free M st).1 (W4En.free M st).2

/-- the call environment at the entry (`RSP = sp + 0x498`; window `[sp - K, sp + 0x510)`) -/
@[reducible] def NEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x498) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ 41640 ≤ K ∧ K + 0x98 ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs sp K 0x510 s.mem ∧ RunIface.Serves R

/-- `z` kept by the alias test: writable, held, apart from the window, the guard and TLS words, the stack, the
operands and the threshold globals -/
@[reducible] def ZOK (R : RtInv) (L : List (Nat × Nat)) (g fs sp K st zp zc xp xc yp yl mp n : Nat)
    (M : Janus.Arm64.Memory) : Prop :=
  NE R L sp K st M zp (8 * zc) ∧ M.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧
    NatLive M R L zp zc ∧ Apart (g + 16) 8 zp (8 * zc) ∧ Apart (fs - 8) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) xp (8 * xc) ∧
    Apart zp (8 * zc) RunIface.gA 32

/-- **the amd64 exp-chain extra entry facts** (coordinator DECISION, NOTES-conventions; divmc's `P2W2.EX` + asm s59):
(a) `x` apart from the threshold globals `gA` (32 bytes), (b) the `natOne` word apart from `gA`, (c) `hasADX` readable
(`Callees.adxAddr = MontHyp.hasADX = 0xbb6b8a`), (d) `x`'s full-capacity range: readable, apart from the stack header
and from the stack's free part. Memory `m` = the entry memory of the function taking it. -/
@[reducible] def XG (m : Janus.Arm64.Memory) (st xp xl xc : Nat) : Prop :=
  (0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (m.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 ∧
  m.accessible Callees.adxAddr 1 false = true ∧
  m.accessible xp (8 * xc) false = true ∧ Apart xp (8 * xc) st 24 ∧
  Apart xp (8 * xc) (W4En.free m st).1 (W4En.free m st).2

/-- the precondition's facts (entry state `s`, `sp = RSP - 0x498`, stack-size and cost parameters of the callees) -/
def NPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - K, sp + 0x510)] ∧
  Outside StackNat.wT 16 R.rt ∧ Outside W4En.wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧ slow = 0 ∧
  s.mem.readLE (sp + 0x4a0) 8 = yp ∧ s.mem.readLE (sp + 0x4a8) 8 = yl ∧ s.mem.readLE (sp + 0x4b0) 8 = yc ∧
  s.mem.readLE (sp + 0x4b8) 8 = mp ∧ s.mem.readLE (sp + 0x4c0) 8 = n ∧ s.mem.readLE (sp + 0x4c8) 8 = mc ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  NE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  NE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ yl ≤ 2 ^ 9 ∧ yc < 2 ^ 64 ∧
  NE R L sp K st s.mem xp (8 * xc) ∧ s.mem.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ zl ≤ zc ∧ zc < 2 ^ 40 ∧
  ((0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨
    ZOK R L g fs sp K st zp zc xp xc yp yl mp n s.mem) ∧ Outside zp (8 * zc) [(sp - K, sp + 0x510)]) ∧
  NE R L sp K st s.mem RunIface.gA 32 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - K, sp + 0x510), (zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
    NHyp.StkApart s.mem st op 8) ∧
  0 < st ∧ st < 2 ^ 48 ∧ StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 0x510) ∧ Apart st 24 (g + 16) 8 ∧
  Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 0x510) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (W4En.free s.mem st).1 (W4En.free s.mem st).2 ∧
  Apart (W4En.free s.mem st).1 (W4En.free s.mem st).2 RunIface.gA 32 ∧
  Apart (W4En.free s.mem st).1 (W4En.free s.mem st).2 (fs - 8) 8 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  stLen s.mem st + needR xl n ≤ 2 ^ 16 ∧ stLen s.mem st + needS xl yl n ≤ 2 ^ 16 ∧
  stLen s.mem st + needP xl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16 ∧
  makeCost 1 + max (costR (stLen s.mem st) xl n) (makeCost n + max (costS (stLen s.mem st) xl yl n)
    (costP (stLen s.mem st) xl yl (Nat.log2 (natVal s.mem mp n)))) ≤ b ∧
  ExpOdd.OBud costF n costD xl yl (stLen s.mem st) (b - makeCost n) ∧
  R.inv b L g (view R.rt L s.mem) ∧
  XG s.mem st xp xl xc

/-- the cost the postcondition charges (an upper bound of every path's; PATH MAX, expmc s44: Go runs `setWord`, or
`z.rem` (y = 1), or `z.make(len m)` and ONE of Slow / Odd / P2 / Even, nat.go:639-720) -/
def NCost (costD : Nat) (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (xl yl n l lm : Nat) : Nat :=
  makeCost 1 + max (costR l xl n) (makeCost n + max (costS l xl yl n) (max (costP l xl yl lm) (ExpOdd.OCost n xl yl costD l)))

/-- the precondition (entry state `s`; register arguments `[z, zl, zc, st, x, xl, xc, slow]`, stack arguments `y`,
`m` read from `RSP + 8 …` in `NPre`) -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NPre R b L K costF costD needR costR needS needP costS costP (s.regs 14).toNat s.fsBase.toNat
    ((s.regs 4).toNat - 0x498) zp zl zc st xp xl xc yp yl yc mp n mc slow s ∧
  (natVal s.mem mp n % 2 = 1 ∨ ∃ k, natVal s.mem mp n = 2 ^ k) ∧ NHyp.XFacts R L xp xl xc

/-- the postcondition (results `RAX, RBX, RCX`), with the goroutine `g` explicit -/
@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (costR : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) (g zp zc st xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (c < 2 ^ 40 ∧ p < 2 ^ 64) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - NCost costD costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)) ≤ b' ∧
      R.inv b' L' g (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s (K + 0x498) 0x78 ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the postcondition: `FS` base and `DF` kept, and `PostG` -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (costR : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) (zp zc st xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
    PostG R b L K costD costR costS costP (s.regs 14).toNat zp zc st xp xl yp yl mp n s s'

end FvModexp.Amd64.ExpN
