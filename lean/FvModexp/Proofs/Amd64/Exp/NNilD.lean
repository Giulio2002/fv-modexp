import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Amd64.Nat.DivMStk

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil` (the path `(*Int).exp` takes): statement layer (agent expmc s73; twin of
`Arm64.ExpN` NNilD + NFunNFD)

`z.expNN(nil, x, y, m, false)` (nat.go:639-722): `getStack()` (`sync.(*Pool).Get(&stackPool)`, nat.go:287) or a new
`*stack` (`newobject(type:big.stack)`), the same computation as the stack-given path on that stack, then the deferred
`stk.free()` (`nat.expNN.deferwrap1`: `len := 0`, `sync.(*Pool).Put`).

* `NE0` / `ZOK0`: `NDefs.NE` / `ZOK` without the stack conjuncts (there is no stack at the entry).
* `PreNil`: `NDefs.NPre` with `st = 0` and without the stack block, for the call `(*Int).exp` makes (`x = z`:
  `xp = zp ∧ xl = zl ∧ xc = zc`); the facts locating `x`, `y` are stated only for a positive length (a nil operand is
  never dereferenced: the trivial cases `len(y) == 0`, `len(x) == 0` return before the stack is taken); `natOne` only
  for a non-empty `z` (`z = x` is non-empty on the stack path); the pool's `New` word is `0` and `0` is not a runtime
  object (`RunIface.PoolG`); the budget carries the 24 bytes of a new `*stack`; the `XG` facts that do not mention
  the stack (`x` vs `gA` is in `NHyp.XFacts`).
* `PostNil`: `NDefs.Post` without the stack conjuncts: value, normalised, `LiveExt` (the stack's ranges, given back to
  the pool, are NOT in the final live set), budget `24 + NCost` at `stLen = 0`, frame `R.rt ++ win ++ [z]`.
* `PreNF` = `PreNil` at `sp = RSP - 0x498` ∧ `NHyp.XFacts` (every modulus) ∧ the `natOne` word outside the window (top s55,
  Janus v0.4.0: the precondition is stated before the return address is installed; for `zc = 0` nothing else keeps
  the word `natOneA` that `PreNil`'s last conjunct reads apart from the return slot); the stack is `DivNil.NewStk`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- an operand at the entry (no stack): held, apart from the window -/
@[reducible] def NE0 (R : RtInv) (L : List (Nat × Nat)) (sp K : Nat) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 0x510)

/-- `ZOK` without the stack conjuncts -/
@[reducible] def ZOK0 (R : RtInv) (L : List (Nat × Nat)) (g fs sp K zp zc xp xc yp yl mp n : Nat)
    (M : Janus.Arm64.Memory) : Prop :=
  NE0 R L sp K zp (8 * zc) ∧ M.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧
    NatLive M R L zp zc ∧ Apart (g + 16) 8 zp (8 * zc) ∧ Apart (fs - 8) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) xp (8 * xc) ∧
    Apart zp (8 * zc) RunIface.gA 32

/-- the precondition's facts, `stk == nil` (entry state `s`, `sp = RSP - 0x498`) -/
def PreNil (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  NEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - K, sp + 0x510)] ∧
  RunIface.PoolG R s.mem [(sp - K, sp + 0x510)] ∧
  Outside StackNat.wT 16 R.rt ∧ Outside W4En.wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧ slow = 0 ∧
  s.mem.readLE (sp + 0x4a0) 8 = yp ∧ s.mem.readLE (sp + 0x4a8) 8 = yl ∧ s.mem.readLE (sp + 0x4b0) 8 = yc ∧
  s.mem.readLE (sp + 0x4b8) 8 = mp ∧ s.mem.readLE (sp + 0x4c0) 8 = n ∧ s.mem.readLE (sp + 0x4c8) 8 = mc ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  NE0 R L sp K mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  (0 < yl → NE0 R L sp K yp (8 * yl)) ∧ (0 < yl → s.mem.accessible yp (8 * yl) false = true) ∧
    (0 < yl → yp + 8 * yl ≤ 2 ^ 48) ∧ NatNorm s.mem yp yl ∧ yl ≤ 2 ^ 9 ∧ yc < 2 ^ 64 ∧
  (0 < xl → NE0 R L sp K xp (8 * xc)) ∧ (0 < xl → s.mem.accessible xp (8 * xc) false = true) ∧
    (0 < xl → xp + 8 * xc ≤ 2 ^ 48) ∧ NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ (zl ≤ zc ∧ xp = zp ∧ xl = zl ∧ xc = zc) ∧ zc < 2 ^ 40 ∧
  (0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨
    ZOK0 R L g fs sp K zp zc xp xc yp yl mp n s.mem) ∧
  (0 < zc → Apart (g + 16) 8 zp (8 * zc) ∧ Apart (fs - 8) 8 zp (8 * zc)) ∧
  NE0 R L sp K RunIface.gA 32 ∧
  (0 < zc → ∃ op, EvenHyp.NatOne R L s.mem op [(sp - K, sp + 0x510), (zp, zp + 8 * zc)]) ∧
  st = 0 ∧ s.mem.accessible StackNat.wbA 4 false = true ∧
  23 * n + 3 ≤ 2 ^ 16 ∧ needR xl n ≤ 2 ^ 16 ∧ needS xl yl n ≤ 2 ^ 16 ∧
  needP xl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16 ∧
  24 + (makeCost 1 + max (costR 0 xl n) (makeCost n + max (costS 0 xl yl n)
    (costP 0 xl yl (Nat.log2 (natVal s.mem mp n))))) ≤ b ∧
  ExpOdd.OBud costF n costD xl yl 0 (b - 24 - makeCost n) ∧
  R.inv b L g (view R.rt L s.mem) ∧
  Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32

/-- the postcondition, `stk == nil` (results `RAX, RBX, RCX`): `FS` base and `DF` kept; as `Post`, without the stack
(returned to the pool) -/
def PostNil (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (costR : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) (zp zc xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (c < 2 ^ 40 ∧ p < 2 ^ 64) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - (24 + NCost costD costR costS costP xl yl n 0 (Nat.log2 (natVal s.mem mp n))) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s (K + 0x498) 0x78 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- the precondition, `stk == nil`, every modulus (register arguments `[z, zl, zc, st, x, xl, xc, slow]`, stack
arguments `y`, `m` read in `PreNil`) -/
def PreNF (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  PreNil R b L K costF costD needR costR needS needP costS costP (s.regs 14).toNat s.fsBase.toNat
    ((s.regs 4).toNat - 0x498) zp zl zc st xp xl xc yp yl yc mp n mc slow s ∧ NHyp.XFacts R L xp xl xc ∧
  Outside EvenHyp.natOneA 8 [((s.regs 4).toNat - 0x498 - K, (s.regs 4).toNat - 0x498 + 0x510)]

end FvModexp.Amd64.ExpN
