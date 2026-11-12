import FvModexp.Proofs.Arm64.Nat.LibMul
import FvModexp.Proofs.Arm64.Nat.SqrDefs
import FvModexp.Proofs.Arm64.Nat.MulAddWW
import FvModexp.Proofs.Common.MulCost

/-!
# The multiplication SCC `{nat.mul, karatsuba, (*Int).mul}` (go-bigmodexpfix natmul.go:16 / :164, int.go:191), arm64 —
statements

`nat.mul(m < n)` calls itself swapped; `nat.mul(m ≥ n ≥ 40)` calls `karatsuba(n)` and, for `n < m`, itself on the chunks
`x[i:i+c]` (`c ≤ n`); `karatsuba(n)` calls `(*Int).mul` three times on operands of `≤ n2 = ⌈n/2⌉` words, which calls
`nat.mul` (`x ≠ y`: karatsuba's operands are distinct frame objects, so `(*Int).mul`'s `x == y` → `nat.sqr` branch is
excluded by the precondition and `nat.sqr` is not in the program). The three summaries are proved together by
`Summary.induction_mutual` with the measure (`k = max(len x, len y)`, `sw = [len x < len y]`)
`μ(nat.mul) = 4·(2k + sw) + 3`, `μ((*Int).mul) = 4·(2k + sw) + 4`, `μ(karatsuba n) = 8n + 2`.
Windows / budgets: `Common/MulCost.lean` (`mulW`, `kW`, `imW`; `mulC`, `KC`).

Frames: `nat.mul` 256 (`SUB $256`; args `z X0-2`, `stk X3`, `x X4-6`, `y X7-9`, spills up to `SP + 88`),
`karatsuba` 448 (args `stk X0`, `z X1-3`, `x X4-6`, `y X7-9`; spills up to `SP + 72`), `(*Int).mul` 96 (args `z X0`,
`stk X1`, `x X2`, `y X3`; spills up to `SP + 40`). The `stk == nil` path of `nat.mul` is refuted by `st ≠ 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep guard)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul"
def fnK : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba"
def fnI : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).mul"
def names : List String := LibMul.names

/-- the operand facts of `z.mul(stk, x, y)` (`z = (zp, ·, zc)`, `x = (xp, xl, xc)`, `y = (yp, yl, yc)`) in memory `m`,
`ws` the window to stay outside of, `g` the goroutine pointer: operands readable, held (cap range), outside `ws`,
apart from the stack's header and free part and the threshold globals; `z` live, is an operand itself (same array and
capacity) or apart from it -/
@[reducible] def Ops (R : RtInv) (L : List (Nat × Nat)) (m : Memory) (g : Nat) (ws : List (Nat × Nat))
    (st zp zc xp xl xc yp yl yc : Nat) : Prop :=
  (xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ m.accessible xp (8 * xl) false = true ∧
    (0 < xc → Held R L xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48) ∧ (0 < xl → Outside xp (8 * xl) ws ∧ StkSep m st xp (8 * xl))) ∧
  (yl ≤ yc ∧ yc < 2 ^ 40 ∧ yl ≤ 2 ^ 12 ∧ m.accessible yp (8 * yl) false = true ∧
    (0 < yc → Held R L yp (8 * yc) ∧ yp + 8 * yc ≤ 2 ^ 48) ∧ (0 < yl → Outside yp (8 * yl) ws ∧ StkSep m st yp (8 * yl))) ∧
  (zc < 2 ^ 40 ∧ NatLive m R L zp zc ∧ Outside zp (8 * zc) ws ∧
    (0 < zc → Apart zp (8 * zc) (g + 16) 8 ∧ StkSep m st zp (8 * zc)) ∧
    ((zp = xp ∧ zc = xc) ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) xp (8 * xl))) ∧
    ((zp = yp ∧ zc = yc) ∨ (0 < zc → 0 < yl → Apart zp (8 * zc) yp (8 * yl)))) ∧
  stLen m st + 4 * (xl + yl) + 64 ≤ 2 ^ 16

/-- **`z.mul(stk, x, y)` precondition** (window `W ≥ mulW xl yl`, `above = 88`); operands need not be normalised -/
def MPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State) : Prop :=
  CallEnv R L s W 88 ∧ mulW xl yl ≤ W ∧ Serves R ∧ Globals R s.mem (win s W 88) ∧ Outside NatAdd.wordT 16 R.rt ∧
    Ops R L s.mem (s.regs 28).toNat (win s W 88) st zp zc xp xl xc yp yl yc ∧ StkPre R L s W 88 st ∧
    mulC (stLen s.mem st) xl yl ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- the exact-write clause: when `z` is large enough and not an operand's alias, the result is `z`'s array, only
`z[0:need]` (and the stack scratch) is written, and `z[0:need]` holds the product (or, on the paths that write nothing,
the product is `0` and `z[0:need]` is unchanged) -/
@[reducible] def Exact (R : RtInv) (L : List (Nat × Nat)) (ws : List (Nat × Nat))
    (need zp zc st xp xc yp yc v p' c' : Nat) (m m' : Memory) : Prop :=
  need ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc → p' = zp ∧ c' = zc ∧
    (natVal m' zp need = v ∨ (v = 0 ∧ natVal m' zp need = natVal m zp need)) ∧
    MemFrame m m' (R.rt ++ ws ++ [(zp, zp + 8 * need)] ++ stkWs m st) ∧
    LiveFrame m m' L ([(zp, zp + 8 * need)] ++ stkWs m st)

/-- `Exact` for `(*Int).mul`: also `z`'s header `[z, z + 32)` is written -/
@[reducible] def ExactI (R : RtInv) (L : List (Nat × Nat)) (ws : List (Nat × Nat))
    (z need zp zc st xp xc yp yc v p' c' : Nat) (m m' : Memory) : Prop :=
  need ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc → p' = zp ∧ c' = zc ∧
    (natVal m' zp need = v ∨ (v = 0 ∧ natVal m' zp need = natVal m zp need)) ∧
    MemFrame m m' (R.rt ++ ws ++ [(z, z + 32), (zp, zp + 8 * need)] ++ stkWs m st) ∧
    LiveFrame m m' L ([(z, z + 32), (zp, zp + 8 * need)] ++ stkWs m st)

/-- **`z.mul(stk, x, y)` postcondition**: `(p', l', c')` in `X0..X2` holds `X·Y` normalised; `z`'s array (always when
it is large enough and not an operand's alias: `Exact`) or a fresh one (apart from the live set and the stack's final
array); the stack is back (`StackBackL`). -/
@[reducible] def MPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧
    s'.regs 2 = BitVec.ofNat 64 c' ∧
    natVal s'.mem p' l' = natVal s.mem xp xl * natVal s.mem yp yl ∧ NatNorm s'.mem p' l' ∧ l' ≤ c' ∧
    l' ≤ xl + yl ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - mulC (stLen s.mem st) xl yl ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (xl + yl ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st →
        Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      Exact R L (winA s W 88) (xl + yl) zp zc st xp xc yp yc (natVal s.mem xp xl * natVal s.mem yp yl) p' c'
        s.mem s'.mem ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st)

/-- **`karatsuba(stk, z, x, y)` precondition** (`len x = len y = n ≥ 40`, `len z = 2n`; reached from `nat.mul` only):
`z` apart from both operands and no alias of either (cap ends differ) -/
def KPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zl zc xp xl xc yp yl yc : Nat) (s : State) : Prop :=
  CallEnv R L s W 72 ∧ kW yl ≤ W ∧ Serves R ∧ Globals R s.mem (win s W 72) ∧ Outside NatAdd.wordT 16 R.rt ∧
    40 ≤ yl ∧ xl = yl ∧ zl = 2 * yl ∧ zl ≤ zc ∧
    Ops R L s.mem (s.regs 28).toNat (win s W 72) st zp zc xp xl xc yp yl yc ∧
    Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧
    zp + 8 * zc ≠ xp + 8 * xc ∧ zp + 8 * zc ≠ yp + 8 * yc ∧
    StkPre R L s W 72 st ∧ KC (stLen s.mem st) yl ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- **`karatsuba(stk, z, x, y)` postcondition**: `z[0:2n] = X·Y` (not normalised), writes only `z[0:2n]`, the stack's
header and free part, the runtime's memory and the window; the stack is back. -/
@[reducible] def KPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zl xp xl yp yl : Nat) (s s' : State) :
    Prop :=
  natVal s'.mem zp zl = natVal s.mem xp xl * natVal s.mem yp yl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - KC (stLen s.mem st) yl ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s W 72 ++ (zp, zp + 8 * zl) :: stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((zp, zp + 8 * zl) :: stkWs s.mem st)

/-- a read-only `*Int` operand header of `(*Int).mul` (kept by the inner `nat.mul`: held, apart from the stack header
and free part) -/
@[reducible] def HdrR (R : RtInv) (L : List (Nat × Nat)) (m : Memory) (ws : List (Nat × Nat)) (st a : Nat) : Prop :=
  hNeg m a ≤ 1 ∧ m.accessible a 32 false = true ∧ a + 32 ≤ 2 ^ 48 ∧ Outside a 32 ws ∧ Held R L a 32 ∧
    Apart a 32 st 24 ∧ Apart a 32 (BasicSqr.freeP m st) (BasicSqr.freeN m st)

/-- **`z.mul(stk, x, y)` (`*Int`) precondition** (`x ≠ y`; window `W ≥ imW`, `above = 40`): headers as `HdrR` (and
`z`'s writable, apart from both operands' headers and arrays and from the stack header), the `abs` triples satisfy `Ops` -/
def IPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W z st x y : Nat) (s : State) : Prop :=
  CallEnv R L s W 40 ∧ imW (hL s.mem x) (hL s.mem y) ≤ W ∧ Serves R ∧ Globals R s.mem (win s W 40) ∧
    Outside NatAdd.wordT 16 R.rt ∧ x ≠ y ∧
    HdrR R L s.mem (win s W 40) st x ∧ HdrR R L s.mem (win s W 40) st y ∧
    s.mem.accessible z 32 true = true ∧ z + 32 ≤ 2 ^ 48 ∧ Outside z 32 (win s W 40) ∧ Held R L z 32 ∧
    Apart z 32 ((s.regs 28).toNat + 16) 8 ∧ Apart z 32 wbA 4 ∧ Apart z 32 x 32 ∧ Apart z 32 y 32 ∧
    Apart z 32 st 24 ∧ s.mem.accessible wbA 4 false = true ∧
    (0 < hC s.mem z → Apart (hP s.mem z) (8 * hC s.mem z) x 32 ∧ Apart (hP s.mem z) (8 * hC s.mem z) y 32 ∧
      Apart (hP s.mem z) (8 * hC s.mem z) z 32) ∧
    Ops R L s.mem (s.regs 28).toNat (win s W 40) st (hP s.mem z) (hC s.mem z) (hP s.mem x) (hL s.mem x) (hC s.mem x)
      (hP s.mem y) (hL s.mem y) (hC s.mem y) ∧
    StkPre R L s W 40 st ∧ mulC (stLen s.mem st) (hL s.mem x) (hL s.mem y) ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- **`z.mul(stk, x, y)` (`*Int`) postcondition**: `z = x·y` (signed, canonical sign), `z.abs` normalised in its old
array (always when large enough and not an alias: `Exact`, with `z`'s header) or a fresh one; the stack is back -/
@[reducible] def IPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W z st x y : Nat) (s s' : State) : Prop :=
  intZ s'.mem z = intZ s.mem x * intZ s.mem y ∧ hNeg s'.mem z ≤ 1 ∧ (hNeg s'.mem z = 1 → 0 < hL s'.mem z) ∧
    NatNorm s'.mem (hP s'.mem z) (hL s'.mem z) ∧ hL s'.mem z ≤ hC s'.mem z ∧
    hL s'.mem z ≤ hL s.mem x + hL s.mem y ∧ hC s'.mem z < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - mulC (stLen s.mem st) (hL s.mem x) (hL s.mem y) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' (hP s'.mem z) (hC s'.mem z) ∧
      ((hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) ∨
        (hL s.mem x + hL s.mem y ≤ hC s'.mem z ∧ InRanges (hP s'.mem z) (8 * hC s'.mem z) R.rt ∧
          ApartAll (hP s'.mem z) (8 * hC s'.mem z) L)) ∧
      (¬ (hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) → 0 < hC s'.mem z → 0 < stCap s'.mem st →
        Apart (hP s'.mem z) (8 * hC s'.mem z) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      ExactI R L (winA s W 40) z (hL s.mem x + hL s.mem y) (hP s.mem z) (hC s.mem z) st (hP s.mem x)
        (hC s.mem x) (hP s.mem y) (hC s.mem y)
        (natVal s.mem (hP s.mem x) (hL s.mem x) * natVal s.mem (hP s.mem y) (hL s.mem y))
        (hP s'.mem z) (hC s'.mem z) s.mem s'.mem ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s W 40 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * hC s.mem z)] ++
        stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(z, z + 32), (hP s.mem z, hP s.mem z + 8 * hC s.mem z)] ++ stkWs s.mem st)

/-! ## The SCC as one family of summaries -/

/-- a member's call: budget, live set, window and the ten argument registers -/
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
  a7 : BitVec 64
  a8 : BitVec 64
  a9 : BitVec 64

/-- the members -/
inductive Tag where
  | mul
  | kar
  | imul

/-- `(.mul, a)`: `nat.mul` (`z = a0..a2`, `stk = a3`, `x = a4..a6`, `y = a7..a9`); `(.kar, a)`: `karatsuba`
(`stk = a0`, `z = a1..a3`, `x = a4..a6`, `y = a7..a9`); `(.imul, a)`: `(*Int).mul` (`z = a0`, `stk = a1`, `x = a2`,
`y = a3`) -/
abbrev Mem : Type := Tag × Args

def entryOf : Mem → Nat
  | (.mul, _) => 0x1bae70
  | (.kar, _) => 0x1bbe70
  | (.imul, _) => 0x1b0c50

theorem entry_mul : segAddr Extracted.program fn = 0x1bae70 := by decide
theorem entry_kar : segAddr Extracted.program fnK = 0x1bbe70 := by decide
theorem entry_imul : segAddr Extracted.program fnI = 0x1b0c50 := by decide

/-- the return-address facts and the argument registers at a member's entry -/
@[reducible] def Entry (a : Args) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = a.a0 ∧ s.regs 1 = a.a1 ∧ s.regs 2 = a.a2 ∧
    s.regs 3 = a.a3 ∧ s.regs 4 = a.a4 ∧ s.regs 5 = a.a5 ∧ s.regs 6 = a.a6 ∧ s.regs 7 = a.a7 ∧ s.regs 8 = a.a8 ∧
    s.regs 9 = a.a9

def preOf (R : RtInv) : Mem → State → Prop
  | (.mul, a), s => Entry a s ∧
      MPre R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat s
  | (.kar, a), s => Entry a s ∧
      KPre R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat
        a.a8.toNat a.a9.toNat s
  | (.imul, a), s => Entry a s ∧ IPre R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat s

/-- the callee-saved part of every member's post -/
@[reducible] def Kept (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18

def postOf (R : RtInv) : Mem → State → State → Prop
  | (.mul, a), s, s' => Kept s s' ∧
      MPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat s s'
  | (.kar, a), s, s' => Kept s s' ∧
      KPost R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a4.toNat a.a5.toNat a.a7.toNat a.a8.toNat s s'
  | (.imul, a), s, s' => Kept s s' ∧ IPost R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat a.a3.toNat s s'

/-- the measure of a pair of lengths: `4·(2·max + [xl < yl])` -/
@[reducible] def μl (xl yl : Nat) : Nat := 4 * (2 * max xl yl + if xl < yl then 1 else 0)

/-- the measure (see the module doc) -/
def μ : Mem → State → Nat
  | (.mul, a), _ => μl a.a5.toNat a.a8.toNat + 3
  | (.kar, a), _ => 8 * a.a8.toNat + 2
  | (.imul, a), s => μl (hL s.mem a.a2.toNat) (hL s.mem a.a3.toNat) + 4

/-- the induction hypothesis of a member proof at measure `n`, for one member -/
@[reducible] def IH (impl : List Segment) (R : RtInv) (n : Nat) (j : Mem) : Prop :=
  Summary (LibMul.program.link impl) (entryOf j) (fun s => preOf R j s ∧ μ j s < n) (postOf R j)

/-! ## The measure decreases along every call -/

theorem μ_swap {m n : Nat} (h : m < n) : μl n m + 3 < μl m n + 3 := by
  unfold μl; rw [if_pos h, if_neg (by omega)]; omega

theorem μ_kar {m n : Nat} (h : n ≤ m) : 8 * n + 2 < μl m n + 3 := by
  unfold μl; omega

theorem μ_chunk {m n c : Nat} (hc : c ≤ n) (h : n < m) : μl c n + 3 < μl m n + 3 := by
  unfold μl; split <;> split <;> omega

theorem μ_inner {n a b : Nat} (h40 : 40 ≤ n) (ha : a ≤ kh n) (hb : b ≤ kh n) : μl a b + 4 < 8 * n + 2 := by
  have : kh n = (n + 1) / 2 := rfl
  unfold μl; split <;> omega

theorem μ_imul (a b : Nat) : μl a b + 3 < μl a b + 4 := by omega

end FvModexp.Arm64.NatMul
