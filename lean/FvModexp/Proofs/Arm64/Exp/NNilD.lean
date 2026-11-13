import FvModexp.Proofs.Arm64.Exp.NGet

/-!
# `nat.expNN` (arm64), `stk == nil` (the path `(*Int).exp` takes): statement layer

`z.expNN(nil, x, y, m, false)` (nat.go:639-722): `getStack()` (`sync.(*Pool).Get(&stackPool)`, nat.go:287) or a new
`*stack` (`newobject(type:big.stack)`), the same computation as the stack-given path on that stack, then the deferred
`stk.free()` (`nat.expNN.deferwrap1`: `len := 0`, `sync.(*Pool).Put`).

* `NE0` / `ZOK0`: `NDefs.NE` / `ZOK` without the stack conjuncts (there is no stack at the entry).
* `PreNil`: `NDefs.NPre` with `st = 0` and without the stack block, for the call `(*Int).exp` makes (`x = z`:
  `xp = zp ∧ xl = zl ∧ xc = zc`); the facts locating `x`, `y` (`z`) are stated only for a positive length (capacity) —
  a nil operand (`(0, 0, 0)`, e.g. `Run`'s exponent of length 0) is never dereferenced (the trivial cases `len(y) == 0`,
  `len(x) == 0` return before the stack is taken), and `natOne` only matters when `z`'s array exists, since with
  `x = z` an empty `z` means `len(x) = 0`; the stack-size bounds and the budget at
  `stLen = 0`, the budget also pays the 24-byte `newobject`; `z`'s array (when non-empty) is held and apart from the
  window even when the alias test drops it (at `(*Int).exp`'s call it is the receiver's live array), and `z`'s range is
  apart from the goroutine's stack-guard word (the deferred `stk.free()` runs after `z` may have been written); address 0 is not a runtime object (`Outside 0 1 R.rt`: `newobject`'s result is non-nil); the pool's `New` word is `0` (the `Get` pre) and lies
  outside the window.
* `PostNil`: `NDefs.Post` without the stack conjuncts: value, normalised, `LiveExt` (the stack's ranges, given back to
  the pool, are NOT in the final live set), budget `24 + NCost` at `stLen = 0`, frame `R.rt ++ winA ++ [z]`.
* `NewStk`: the stack after `Get`/`newobject` (both cases), at the memory of the `rem` entry / `J5`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- an operand at the entry (no stack): held, apart from the window -/
@[reducible] def NE0 (R : RtInv) (L : List (Nat × Nat)) (sp K : Nat) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 1432)

/-- `ZOK` without the stack conjuncts -/
@[reducible] def ZOK0 (R : RtInv) (L : List (Nat × Nat)) (g sp K zp zc xp xl yp yl mp n : Nat) (M : Memory) : Prop :=
  NE0 R L sp K zp (8 * zc) ∧ M.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧
    NatLive M R L zp zc ∧ Apart (g + 16) 8 zp (8 * zc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
    Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) RunIface.gA 32

/-- the precondition's facts, `stk == nil` (entry state `s`, `sp = SP - 1312`) -/
def PreNil (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (g sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NEnv R L g sp K s ∧ K + 288 ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 1432)] ∧ (RoOut R ∧ Outside 0 1 R.rt) ∧
  Outside StackNat.wT 16 R.rt ∧ slow = 0 ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  NE0 R L sp K mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  (0 < yl → NE0 R L sp K yp (8 * yl)) ∧ (0 < yl → s.mem.accessible yp (8 * yl) false = true) ∧
    (0 < yl → yp + 8 * yl ≤ 2 ^ 48) ∧ NatNorm s.mem yp yl ∧ yl ≤ 2 ^ 9 ∧ (yc < 2 ^ 64 ∧ yp < 2 ^ 64) ∧
  (0 < xl → NE0 R L sp K xp (8 * xl)) ∧ (0 < xl → s.mem.accessible xp (8 * xl) false = true) ∧
    (0 < xl → xp + 8 * xl ≤ 2 ^ 48) ∧ NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ (zl ≤ zc ∧ xp = zp ∧ xl = zl ∧ xc = zc) ∧ zc < 2 ^ 40 ∧
  ((0 < zc → Apart (g + 16) 8 zp (8 * zc)) ∧ (0 < zc → NE0 R L sp K zp (8 * zc))) ∧
  (0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨
    ZOK0 R L g sp K zp zc xp xl yp yl mp n s.mem) ∧
  NE0 R L sp K RunIface.gA 32 ∧
  (0 < zc → ∃ op, EvenHyp.NatOne R L s.mem op [(sp - K, sp + 1432), (zp, zp + 8 * zc)]) ∧
  st = 0 ∧ s.mem.accessible StackNat.wbA 4 false = true ∧
  StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧
  needR xl n ≤ 2 ^ 16 ∧ needS xl yl n ≤ 2 ^ 16 ∧ needP xl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16 ∧
  24 + (makeCost 1 + max (costR 0 xl n) (makeCost n + max (costS 0 xl yl n)
    (max (costP 0 xl yl (Nat.log2 (natVal s.mem mp n))) (ExpOdd.OBud costF n xl yl 0)))) ≤ b ∧
  s.mem.readLE (Free.poolA + newOffset) 8 = 0 ∧ Outside (Free.poolA + newOffset) 8 [(sp - K, sp + 1432)] ∧
  R.inv b L g (view R.rt L s.mem)

/-- the postcondition, `stk == nil` (results `X0..X2`): as `Post`, without the stack (returned to the pool) -/
def PostNil (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zc xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (c < 2 ^ 40 ∧ p < 2 ^ 64) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - (24 + NCost costF costR costS costP xl yl n 0 (Nat.log2 (natVal s.mem mp n))) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 1312) 120 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- the new stack `st` (from `Get` or `newobject`) at memory `M1`: its ranges `stkRs M1 st` are fresh runtime
objects added to the live set (`L1 = L ++ stkRs M1 st`), it is empty (`len = 0`), of the pool shape; budget at most
the 24 bytes of `newobject` less -/
def NewStk (R : RtInv) (L L1 : List (Nat × Nat)) (b b1 : Nat) (g : Nat) (M1 : Memory) (st : Nat) : Prop :=
  L1 = L ++ stkRs M1 st ∧ (∀ x ∈ stkRs M1 st, InRanges x.1 (x.2 - x.1) R.rt ∧ ApartAll x.1 (x.2 - x.1) L) ∧
  0 < st ∧ st % 8 = 0 ∧ st + 24 ≤ 2 ^ 48 ∧ M1.accessible st 24 true = true ∧ stLen M1 st = 0 ∧
  stCap M1 st < 2 ^ 40 ∧ (stCap M1 st = 0 → stW M1 st = 0) ∧ stW M1 st % 8 = 0 ∧
  stW M1 st + 8 * stCap M1 st ≤ 2 ^ 48 ∧
  (0 < stCap M1 st → M1.accessible (stW M1 st) (8 * stCap M1 st) true = true) ∧
  Apart st 24 (stW M1 st) (8 * stCap M1 st) ∧ b ≤ b1 + 24 ∧ b1 ≤ b ∧
  R.inv b1 L1 g (view R.rt L1 M1)

end FvModexp.Arm64.ExpN
