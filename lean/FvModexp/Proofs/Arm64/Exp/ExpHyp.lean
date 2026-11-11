import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.ExpHypVal
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Arm64.Nat.StackNatDefs

/-!
# Callee premises of the exponentiation layer (arm64), CONVENTIONS §3 shape — hypotheses until the owners land theirs

`nat.cmp`, `nat.sub`, `nat.lsh`, `nat.div` (divmc) and `(*stack).nat` (top) as `Ensures` premises in the §3 shape with the
bounded `RunIface.Serves R`. Each is parametric in the callee's `names` (`ns`, any list the owner's proof uses; the caller
only needs `ns ⊆ LibExp.names`), its stack bound `stk` and spill bound `above`, so that the owner's `ens` instantiates
the premise directly. Values are the pre-state values (`natVal s.mem …`); results as Go returns them (`X0..`).
Stack object (top's `stackOK`): header `(w, len, cap)` at `st`, `w` = the array (held, writable when `cap > 0`).
Shapes posted in /srv/fv-modexp-ops/NOTES-conventions.md ([expmc s3] callee shapes).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpHyp

open FvModexp.Arm64.RunIface (Serves P)

/-- a read-only input array `p[0:n]` of a callee whose window is `win s stk above` -/
@[reducible] def RdIn (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above p n : Nat) : Prop :=
  n < 2 ^ 40 ∧ s.mem.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ Held R L p (8 * n) ∧
    Outside p (8 * n) (win s stk above)

/-- a reused output array `p[0:c]` (CONVENTIONS §5, §8c) -/
@[reducible] def WrOut (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive s.mem R L p c ∧ (0 < c → Outside p (8 * c) (win s stk above) ∧
    Apart p (8 * c) ((s.regs 28).toNat + 16) 8)

/-- the result nat `(p', l', c')` of a function that reuses `z = (zp, zc)` when `zc ≥ need` and allocates otherwise -/
@[reducible] def NatRes (R : RtInv) (L L' : List (Nat × Nat)) (m' : Memory) (zp zc need p' l' c' v : Nat) : Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    (need ≤ zc → p' = zp ∧ c' = zc) ∧
    (zc < need → 0 < c' → InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)

/-- the runtime-side post of every shape: live set grown, budget, invariant -/
@[reducible] def RtPost (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat)) (b' : Nat) (s s' : State) : Prop :=
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)

/-! ## `x.cmp(y)` (nat.go:84) — X0..X2 = x, X3..X5 = y; result X0 -/

def fnCmp : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.cmp"

@[reducible] def CmpPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above x xl y yl : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ RdIn R L s stk above x xl ∧ RdIn R L s stk above y yl ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def CmpPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above x xl y yl : Nat) (s s' : State) :
    Prop :=
  s'.regs 0 = BitVec.ofInt 64 (Exp.cmpVal xl yl (natVal s.mem x xl) (natVal s.mem y yl)) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), RtPost R b 0 L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above) ∧ LiveFrame s.mem s'.mem L []

def CmpHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnCmp) [x, xl, xc, y, yl, yc]
      (fun s => CmpPre R b L stk above x.toNat xl.toNat y.toNat yl.toNat s)
      (fun s s' => CmpPost R b L stk above x.toNat xl.toNat y.toNat yl.toNat s s')

/-! ## `z.sub(x, y)` (nat.go:144; `x ≥ y`, `y` normalised, else it panics) — z X0..X2, x X3..X5, y X6..X8 -/

def fnSub : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sub"

@[reducible] def SubPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl y yl : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    RdIn R L s stk above x xl ∧ RdIn R L s stk above y yl ∧ xl ≤ 2 ^ 16 ∧
    (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧ (0 < zc → 0 < yl → Apart zp (8 * zc) y (8 * yl)) ∧
    NatNorm s.mem y yl ∧ natVal s.mem y yl ≤ natVal s.mem x xl ∧ makeCost xl ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def SubPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl y yl : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc xl p' l' c' (natVal s.mem x xl - natVal s.mem y yl) ∧ RtPost R b (makeCost xl) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

def SubHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSub)
      [z, zl, zc, x, xl, xc, y, yl, yc]
      (fun s => SubPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat y.toNat yl.toNat s)
      (fun s s' => SubPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat y.toNat yl.toNat s s')

/-! ## `z.lsh(x, sh)` (nat.go:432) — z X0..X2, x X3..X5, sh X6; result `x · 2^sh` normalised -/

def fnLsh : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.lsh"

@[reducible] def LshPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl sh : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl + sh / 64 + 1 ≤ 2 ^ 16 ∧ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl)) ∧
    makeCost (xl + sh / 64 + 1) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def LshPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (xl + sh / 64 + 1) p' l' c' (natVal s.mem x xl * 2 ^ sh) ∧
      RtPost R b (makeCost (xl + sh / 64 + 1)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

def LshHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnLsh) [z, zl, zc, x, xl, xc, sh]
      (fun s => LshPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s)
      (fun s s' => LshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

/-! ## The `*stack` object (top's `stackOK`) -/

/-- the stack header reads, `stackOK` and the written ranges are divmc's `FvModexp.stW/stLen/stCap`, `StkOK`, `stkWs`
(Common/StackScr.lean); the names below are kept as abbreviations. -/
@[reducible] def StackOK' (m : Memory) (R : RtInv) (L : List (Nat × Nat)) (st : Nat) : Prop := StkOK m R L st
@[reducible] def stWs (m : Memory) (st : Nat) : List (Nat × Nat) := stkWs m st

/-! ## `stk.nat(n)` (nat.go:?? `(*stack).nat`, top) — X0 = st, X1 = n; result the new nat `(w' + 8 len, n, n)` -/

abbrev fnStackNat : String := StackNat.fn

/-- top's `B_nat n` budget bound — now `FvModexp.stackNatCost` (Common/StackNatMath.lean) -/
abbrev stackNatCost (len n : Nat) : Nat := FvModexp.stackNatCost len n

/-- `(*stack).nat`'s statement: divmc's PROVED shape `FvModexp.Arm64.StackNat.{Pre,Post,Hyp}` (Arm64/Nat/StackNatDefs.lean;
expmc's original shape amended there: write-barrier flag readable and apart from the header, header apart from the free
part, `X0` for `0 < n`, "kept"/"fresh" split at `len + nr` vs `cap`). Proof: `FvModexp.Arm64.StackNat.hyp`. -/
abbrev StackNatPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s : State) : Prop :=
  StackNat.Pre R b L stk above st n s

abbrev StackNatPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s s' : State) : Prop :=
  StackNat.Post R b L stk above st n s s'

abbrev StackNatHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  StackNat.Hyp impl R ns stk above

/-! ## `z.div(stk, z2, u, v)` (natdiv.go:?? `nat.div`, divmc) — z X0..X2, st X3, z2 X4..X6, u X7..X9, v X10..X12;
results q X0..X2 = `u / v`, r X3..X5 = `u % v` (both normalised). `u`, `v` normalised, `v ≠ 0`. -/

def fnDiv : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div"

/-- closed budget bound of one `div` with operands of at most `ul` words (divmc fixes it; a parameter here) -/
@[reducible] def DivPre (R : RtInv) (b cost : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st z2 z2l z2c u ul v vl : Nat)
    (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    stLen s.mem st + 4 * ul + 64 ≤ 2 ^ 16 ∧
    -- pairwise: the outputs are apart from each other, from the inputs and from the stack's free part / header
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    cost ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def DivPost (R : RtInv) (b cost : Nat) (L : List (Nat × Nat)) (stk above zp zc st z2 z2c u ul v vl : Nat)
    (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (ul + 1) q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatRes R L L' s'.mem z2 z2c (ul + 1) r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b cost L L' b' s s' ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

def DivHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat
        ul.toNat v.toNat vl.toNat s)
      (fun s s' => DivPost R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat
        vl.toNat s s')

end FvModexp.Arm64.ExpHyp
