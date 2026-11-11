import FvModexp.Proofs.Arm64.Exp.EvenHyp

/-!
# `nat.sqr` / `nat.mul` (owner divmc) and alias-allowed `nat.lsh` (owner asm) as premises (arm64; agent infra)

Shapes follow divmc's PLANNED `nat.mul` shape (NOTES-divmc "PLANNED `nat.mul` shape"), parametric in the owner's `ns`,
`stk`, `above` and a cost function, as expmc's `ExpHyp` premises. Differences a caller needs (modularInverseModPowerOfTwo,
nat.go:1287): the operands need NOT be normalised (`z.sqr(stk, z)` on the `numWords + 1` words left by `z.make`,
`zz.mul(stk, zz, x[:min(i, lenX)])` on a prefix of `x`); `z` may be the same slice as an operand (Go: `alias → z = nil`);
the result is old-or-fresh (`NatOF`). `nat.lsh` with `z = x` (`z = z.lsh(z, 1)`, nat.go:1331) — expmc's `LshHyp` requires
`z` apart from `x`; Go's `shlVU` shifts in place, so `LshPreA` allows `zp = x`.

Stack object `st` (`*stack`, non-nil): `StkOK`, header and array outside the callee window, operands and `z` apart from
the header and the free part; the scratch use is undone (`StackBack`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes NatOF RtPost StackOK' stWs LshPost fnLsh)

/-- the `*stack` object as a scratch user needs it (as `ExpHyp.DivPre`) -/
@[reducible] def StkIn (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st : Nat) : Prop :=
  StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8)

/-- an array `(p, c)` apart from the stack's header and free part -/
@[reducible] def StkApart (m : Memory) (st p c : Nat) : Prop :=
  0 < c → Apart p c st 24 ∧ Apart p c (stW m st + 8 * stLen m st) (8 * (stCap m st - stLen m st))

/-! ## `z.sqr(stk, x)` (nat.go:? `nat.sqr`) — z X0..X2, st X3, x X4..X6; result `X²` normalised -/

def fnSqr : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr"

@[reducible] def SqrPre (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st x xl : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    RdIn R L s stk above x xl ∧ xl ≤ 2 ^ 12 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    StkIn R L s stk above st ∧ stLen s.mem st + 4 * (2 * xl) + 64 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st x (8 * xl) ∧
    c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def SqrPost (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (2 * xl) p' l' c' (natVal s.mem x xl * natVal s.mem x xl) ∧
      RtPost R b c L L' b' s s' ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

/-- `cost xl`: the owner's budget bound of one `sqr` of an `xl`-word operand -/
def SqrHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPre R b (cost xl.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat s)
      (fun s s' => SqrPost R b (cost xl.toNat) L stk above z.toNat zc.toNat st.toNat x.toNat xl.toNat s s')

/-! ## `z.mul(stk, x, y)` (nat.go:? `nat.mul`) — z X0..X2, st X3, x X4..X6, y X7..X9; result `X · Y` normalised -/

def fnMul : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul"

@[reducible] def MulPre (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st x xl y yl : Nat)
    (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    RdIn R L s stk above x xl ∧ RdIn R L s stk above y yl ∧ xl ≤ 2 ^ 12 ∧ yl ≤ 2 ^ 12 ∧
    (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    (zp = y ∨ (0 < zc → 0 < yl → Apart zp (8 * zc) y (8 * yl))) ∧
    StkIn R L s stk above st ∧ stLen s.mem st + 4 * (xl + yl) + 64 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st x (8 * xl) ∧ StkApart s.mem st y (8 * yl) ∧
    c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def MulPost (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl y yl : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (xl + yl) p' l' c' (natVal s.mem x xl * natVal s.mem y yl) ∧
      RtPost R b c L L' b' s s' ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

/-- `cost xl yl`: the owner's budget bound of one `mul` -/
def MulHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre R b (cost xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat
        y.toNat yl.toNat s)
      (fun s s' => MulPost R b (cost xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat
        yl.toNat s s')

/-! ## `z.lsh(x, sh)` with `z = x` allowed — expmc's `LshPost` -/

@[reducible] def LshPreA (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl sh : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl + sh / 64 + 1 ≤ 2 ^ 16 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (xl + sh / 64 + 1) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

def LshHypA (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnLsh) [z, zl, zc, x, xl, xc, sh]
      (fun s => LshPreA R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s)
      (fun s s' => LshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

end FvModexp.Arm64.EvenHyp
