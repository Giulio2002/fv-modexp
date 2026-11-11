import FvModexp.Proofs.Arm64.Nat.LibSqr
import FvModexp.Proofs.Arm64.Nat.BasicSqr
import FvModexp.Proofs.Arm64.Int.IntAS
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.SqrCost

/-!
# The squaring SCC `{nat.sqr, karatsubaSqr}` (go-bigmodexpfix natmul.go:73 / :257), arm64 — statements

`nat.sqr` calls `karatsubaSqr` (`n ≥ 80`), which calls `nat.sqr` three times on operands of `≤ n2 = ⌈n/2⌉` words: the two
summaries are proved together by `Summary.induction_mutual` (PROOFS.md §Mutual recursion) with the measure
`2·len x + 1` (`nat.sqr`) / `2·len x` (`karatsubaSqr`). The index of a member (`Mem`) carries its arguments, budget, live
set and window, so the induction hypothesis covers every call.

Windows: the precondition takes the window `W` as a parameter with `sqrW (len x) ≤ W` (`ksqrW` for `karatsubaSqr`;
`Common/SqrCost.lean`): an inner call one frame down gets `W - frame`, which is again large enough.

`nat.sqr` (args `X0..X2 = z`, `X3 = stk`, `X4..X6 = x`): frame 176 (`MOVD.W R30, -176(RSP)`), spills up to `SP + 64`
(`above = 64`). `karatsubaSqr` (args `X0 = stk`, `X1..X3 = z`, `X4..X6 = x`): frame 320, spills up to `SP + 48`.
The `stk == nil` path of `nat.sqr` (`getStack`, `defer stk.free()`) is refuted by `st ≠ 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

open FvModexp.Arm64.RunIface (Serves Globals)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr"
def fnK : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr"
def names : List String := LibSqr.names

abbrev guard (s : State) : Nat := (s.regs 28).toNat + 16

/-- the stack-object facts every scratch user needs (as `BasicSqr.Pre`): header and array outside the window and apart
from the guard word, the free part apart from the guard word, the header and the `runtime.writeBarrier` flag, and outside
the window -/
@[reducible] def StkPre (R : RtInv) (L : List (Nat × Nat)) (s : State) (W above st : Nat) : Prop :=
  st ≠ 0 ∧ StkOK s.mem R L st ∧ Outside st 24 (win s W above) ∧ Apart st 24 (guard s) 8 ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s W above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) (guard s) 8) ∧
    Apart (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) (guard s) 8 ∧
    Outside (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) (win s W above) ∧
    Apart st 24 (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) ∧ Apart st 24 StackNat.wbA 4

/-- an array `[p, p + n)` apart from the stack's header and free part -/
@[reducible] def StkSep (m : Memory) (st p n : Nat) : Prop :=
  Apart st 24 p n ∧ Apart p n (BasicSqr.freeP m st) (BasicSqr.freeN m st)

/-- **`z.sqr(stk, x)` precondition** (`len x = xl`, `cap x = xc`; `z = (zp, ·, zc)`): `z` is `x` itself (same array and
capacity: Go's `alias` test then allocates) or apart from `x`; operands need not be normalised. -/
def SPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc : Nat) (s : State) : Prop :=
  CallEnv R L s W 64 ∧ sqrW xl ≤ W ∧ Serves R ∧ Globals R s.mem (win s W 64) ∧ Outside NatAdd.wordT 16 R.rt ∧
    xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ s.mem.accessible xp (8 * xl) false = true ∧
    (0 < xc → Held R L xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48) ∧ (0 < xl → Outside xp (8 * xl) (win s W 64)) ∧
    zc < 2 ^ 40 ∧ NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s W 64) ∧
    (0 < zc → Apart zp (8 * zc) (guard s) 8 ∧ StkSep s.mem st zp (8 * zc)) ∧
    ((zp = xp ∧ zc = xc) ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) xp (8 * xl))) ∧
    StkPre R L s W 64 st ∧ (0 < xl → StkSep s.mem st xp (8 * xl)) ∧
    stLen s.mem st + 4 * (2 * xl) + 64 ≤ 2 ^ 16 ∧ sqrC (stLen s.mem st) xl ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- **`z.sqr(stk, x)` postcondition**: `(p', l', c')` in `X0..X2` holds `X²` normalised; the array is `z`'s
(always when `cap z ≥ 2·len x` and `z` is not `x`'s alias, and then exactly `z[0:2·len x]` is written, holding `X²`) or
a fresh one (apart from the live set and from the stack's final array); the stack is back (`StackBack`). -/
@[reducible] def SPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧
    s'.regs 2 = BitVec.ofNat 64 c' ∧
    natVal s'.mem p' l' = natVal s.mem xp xl * natVal s.mem xp xl ∧ NatNorm s'.mem p' l' ∧ l' ≤ c' ∧
    l' ≤ 2 * xl ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - sqrC (stLen s.mem st) xl ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (2 * xl ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st →
        Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      (2 * xl ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → p' = zp ∧ c' = zc ∧
        natVal s'.mem zp (2 * xl) = natVal s.mem xp xl * natVal s.mem xp xl ∧
        MemFrame s.mem s'.mem (R.rt ++ winA s W 64 ++ [(zp, zp + 8 * (2 * xl))] ++ stkWs s.mem st)) ∧
      StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s W 64 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st)

/-- **`karatsubaSqr(stk, z, x)` precondition** (`len x = xl ≥ 80`, `len z = 2·xl`; reached from `nat.sqr` only) -/
def KPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zl zc xp xl xc : Nat) (s : State) : Prop :=
  CallEnv R L s W 48 ∧ ksqrW xl ≤ W ∧ Serves R ∧ Globals R s.mem (win s W 48) ∧ Outside NatAdd.wordT 16 R.rt ∧
    80 ≤ xl ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ s.mem.accessible xp (8 * xl) false = true ∧
    Held R L xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48 ∧ Outside xp (8 * xl) (win s W 48) ∧
    zl = 2 * xl ∧ zl ≤ zc ∧ zc < 2 ^ 40 ∧ NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s W 48) ∧
    Apart zp (8 * zc) (guard s) 8 ∧ StkSep s.mem st zp (8 * zc) ∧ Apart zp (8 * zc) xp (8 * xl) ∧
    zp + 8 * zc ≠ xp + 8 * xc ∧
    StkPre R L s W 48 st ∧ StkSep s.mem st xp (8 * xl) ∧
    stLen s.mem st + 4 * (2 * xl) + 64 ≤ 2 ^ 16 ∧ ksqrC (stLen s.mem st) xl ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- **`karatsubaSqr(stk, z, x)` postcondition**: `z[0:2·len x] = X²` (not normalised), writes only `z[0:2·len x]`, the
stack's header and free part, the runtime's memory and the window; the stack is back. -/
@[reducible] def KPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zl xp xl : Nat) (s s' : State) : Prop :=
  natVal s'.mem zp zl = natVal s.mem xp xl * natVal s.mem xp xl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - ksqrC (stLen s.mem st) xl ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s W 48 ++ (zp, zp + 8 * zl) :: stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((zp, zp + 8 * zl) :: stkWs s.mem st)

/-! ## The SCC as one family of summaries -/

/-- a member's call: budget, live set, window and the seven argument registers -/
structure Args where
  b : Nat
  L : List (Nat × Nat)
  W : Nat
  a0 : BitVec 64
  a1 : BitVec 64
  a2 : BitVec 64
  a3 : BitVec 64
  a4 : BitVec 64
  a5 : BitVec 64
  a6 : BitVec 64

/-- the members: `(false, a)` = `nat.sqr` (`z = a0..a2`, `stk = a3`, `x = a4..a6`), `(true, a)` = `karatsubaSqr`
(`stk = a0`, `z = a1..a3`, `x = a4..a6`) -/
abbrev Mem : Type := Bool × Args

def entryOf : Mem → Nat
  | (false, _) => 0x1bb420
  | (true, _) => 0x1bc2b0

theorem entry_sqr : segAddr Extracted.program fn = 0x1bb420 := by decide
theorem entry_ksqr : segAddr Extracted.program fnK = 0x1bc2b0 := by decide

/-- the argument registers and the return-address facts at a member's entry -/
@[reducible] def Entry (a : Args) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = a.a0 ∧ s.regs 1 = a.a1 ∧ s.regs 2 = a.a2 ∧
    s.regs 3 = a.a3 ∧ s.regs 4 = a.a4 ∧ s.regs 5 = a.a5 ∧ s.regs 6 = a.a6

def preOf (R : RtInv) : Mem → State → Prop
  | (false, a), s => Entry a s ∧
      SPre R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s
  | (true, a), s => Entry a s ∧
      KPre R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s

/-- the callee-saved part of every member's post -/
@[reducible] def Kept (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18

def postOf (R : RtInv) : Mem → State → State → Prop
  | (false, a), s, s' => Kept s s' ∧
      SPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s s'
  | (true, a), s, s' => Kept s s' ∧
      KPost R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a4.toNat a.a5.toNat s s'

/-- the measure: `2·len x + 1` for `nat.sqr`, `2·len x` for `karatsubaSqr` (`sqr → ksqr` at the same length,
`ksqr(n) → sqr(≤ ⌈n/2⌉)`, `n ≥ 80`) -/
def μ : Mem → State → Nat
  | (false, a), _ => 2 * a.a5.toNat + 1
  | (true, a), _ => 2 * a.a5.toNat

/-- the induction hypothesis of a member proof at measure `n`, for one member -/
@[reducible] def IH (impl : List Segment) (R : RtInv) (n : Nat) (j : Mem) : Prop :=
  Summary (LibSqr.program.link impl) (entryOf j) (fun s => preOf R j s ∧ μ j s < n) (postOf R j)

end FvModexp.Arm64.NatSqr
