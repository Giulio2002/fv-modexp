import FvModexp.Proofs.Arm64.Exp.LibCalls
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `buildPrecomputationWindowModPower2` (go-bigmodexpfix nat.go:856-899), arm64 — statement pieces (agent infra)

`buildPrecomputationWindowModPower2(stk, powers, windowSize, logM, x)`: args `stk` X0, `powers` X1..X3, `windowSize` X4,
`logM` X5, `x` X6..X8. Entry `0x1b53d0 = 1790928`. Frame 208 (`MOVD.W R30, -208(RSP)`, FP at `SP - 216`); spills
(from the entry `SP`) `stk` `+8`, `powers.ptr` `+16`, `len` `+24`, `logM` `+48`, `x` `+56 … +72` (`above = 80`);
locals `w = ⌈logM/64⌉` `-64`, `logM + 63` `-56`, `len` `-48`, loop `i` `-88`, `24 i + 24` `-80`, `24 i` `-72`,
`&powers[i+1]` `-24`, `&powers[i]` `-16`. Callees at `SP' = SP - 208`: `stk.nat`, `trunc`, `sqr`, `mul`, `memmove`,
`gcWriteBarrier2`; the callees' spill areas end at `SP' + 88` at most (`above ≤ 88`).

The function: `buf = stk.nat((len+1)·w)`, `powers[i] = buf[i w : (i+1) w : (i+2) w]` (with write barriers),
`powers[0] = set(natOne)[:1:w]`, `powers[1] = trunc(x, logM)[: :w]`, then for `i = 2, 4, …`:
`powers[i] = trunc(sqr(powers[i/2]))[: :w]`, `powers[i+1] = trunc(mul(powers[i], powers[1]))[: :w]`. Every `sqr` / `mul` /
`trunc` reuses its `z` (enough capacity, `z`'s cap end differs from the operands'), so `powers[j]`'s array is
`buf + 8 j w` and the `cap ≥ w` reslice checks never panic. Values: `Exp.p2Pow logM X j` (`= X^j mod 2^logM`).

Statement restrictions (callers `expNNPowerOfTwoWindowSize{2,4}`): `windowSize ∈ {2, 4}`, `len = 2^windowSize`,
`2 ≤ logM ≤ 2^13`, `x` normalised, a non-nil `stk`, `powers` a caller-frame array outside the runtime. The last two
conjuncts of `Pre` (the stack header and free part apart from the threshold globals `gA`) are what `nat.sqr`'s
`StkPre` needs (divmc s13); they are carried for the `sqr` call sites once `SqrHypR` is instantiated with divmc's `ens`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut RtPost StackOK' stWs)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.buildPrecomputationWindowModPower2"

theorem fnBase : segAddr LibExp.program fn = 1790928 := by decide

/-- bytes above `SP` (the 8 argument spill words + the caller's saved-LR slot) -/
abbrev A : Nat := 80

/-- stack bytes below `SP`: the frame plus the deepest callee (`kc`) -/
@[reducible] def K (kc : Nat) : Nat := 208 + kc

/-- `w = ⌈logM / 64⌉` (nat.go:860) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the words of `buf` -/
@[reducible] def NB (pl lm : Nat) : Nat := (pl + 1) * W lm

/-- the stack length inside the loop -/
@[reducible] def ℓ1 (ℓ pl lm : Nat) : Nat := ℓ + StackNat.rnd (NB pl lm)

/-- a `trunc` budget (any result length `≤ w`; `makeCap 0 = 4`) -/
@[reducible] def tC (lm : Nat) : Nat := makeCost (W lm + 4)

/-- one loop round: `sqr`, `mul`, two `trunc`s -/
@[reducible] def rc (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ pl lm : Nat) : Nat :=
  sqC (ℓ1 ℓ pl lm) (W lm) + mlC (ℓ1 ℓ pl lm) (W lm) (W lm) + 2 * tC lm

/-- before the loop: `stk.nat` and `trunc(x)` -/
@[reducible] def c0 (ℓ pl lm : Nat) : Nat := stackNatCost ℓ (NB pl lm) + tC lm

@[reducible] def cost (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ pl lm : Nat) : Nat :=
  c0 ℓ pl lm + (pl / 2 - 1) * rc sqC mlC ℓ pl lm

/-- the ranges the function writes (besides the runtime's) -/
@[reducible] def LW (s : State) (pw pl st : Nat) : List (Nat × Nat) := [(pw, pw + 24 * pl)] ++ stWs s.mem st

@[reducible] def AW (R : RtInv) (kc : Nat) (s : State) (pw pl st : Nat) : List (Nat × Nat) :=
  R.rt ++ winA s (K kc) A ++ LW s pw pl st

@[reducible] def Pre (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (st pw pl ws lm x xl : Nat) (s : State) : Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧ RunIface.Globals R s.mem (winA s (K kc) A ++ [(pw, pw + 24 * pl), (st, st + 24)]) ∧
    (ws = 2 ∨ ws = 4) ∧ pl = 2 ^ ws ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧
    pw % 8 = 0 ∧ pw + 24 * pl ≤ 2 ^ 48 ∧ s.mem.accessible pw (24 * pl) true = true ∧ Outside pw (24 * pl) R.rt ∧
    Outside pw (24 * pl) (win s (K kc) A) ∧ Apart pw (24 * pl) ((s.regs 28).toNat + 16) 8 ∧
    StkApart s.mem st pw (24 * pl) ∧ (0 < xl → Apart pw (24 * pl) x (8 * xl)) ∧
    RdIn R L s (K kc) A x xl ∧ NatNorm s.mem x xl ∧ xl ≤ 2 ^ 12 ∧ StkApart s.mem st x (8 * xl) ∧
    StkIn R L s (K kc) A st ∧ stLen s.mem st + 2 ^ 12 ≤ 2 ^ 16 ∧
    Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    (∃ op, NatOne R L s.mem op (winA s (K kc) A ++ LW s pw pl st) ∧ StkApart s.mem st op 8) ∧
    cost sqC mlC (stLen s.mem st) pl lm ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32

/-- a computed `powers[j]` at memory `M`: header `(bp + 8 j w, l, w)`, `l ≤ w`, value `p2Pow`, normalised -/
@[reducible] def PwD (M : Memory) (pw bp lm X j : Nat) : Prop :=
  M.readLE (pw + 24 * j) 8 = bp + 8 * (j * W lm) ∧ M.readLE (pw + 24 * j + 16) 8 = W lm ∧
    M.readLE (pw + 24 * j + 8) 8 ≤ W lm ∧
    natVal M (bp + 8 * (j * W lm)) (M.readLE (pw + 24 * j + 8) 8) = Exp.p2Pow lm X j ∧
    NatNorm M (bp + 8 * (j * W lm)) (M.readLE (pw + 24 * j + 8) 8)

/-- a not yet computed `powers[j]`: the header the fill loop wrote, `(bp + 8 j w, w, 2 w)` -/
@[reducible] def PwT (M : Memory) (pw bp lm j : Nat) : Prop :=
  M.readLE (pw + 24 * j) 8 = bp + 8 * (j * W lm) ∧ M.readLE (pw + 24 * j + 8) 8 = W lm ∧
    M.readLE (pw + 24 * j + 16) 8 = 2 * W lm

/-- the stack after the call: `len` grown by `rnd NB`, the array the old one or fresh -/
@[reducible] def StkAfter (R : RtInv) (L L' : List (Nat × Nat)) (st ℓ pl lm : Nat) (m0 m : Memory) : Prop :=
  StkOK m R L' st ∧ stLen m st = ℓ + StackNat.rnd (NB pl lm) ∧
    ((stW m st = stW m0 st ∧ stCap m st = stCap m0 st) ∨
      (InRanges (stW m st) (8 * stCap m st) R.rt ∧ ApartAll (stW m st) (8 * stCap m st) L))

@[reducible] def Post (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s s' : State) : Prop :=
  ∃ bp : Nat, (∀ j, j < pl → PwD s'.mem pw bp lm (natVal s.mem x xl) j) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - cost sqC mlC (stLen s.mem st) pl lm ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
      Scr R L L' s.mem s'.mem st bp (NB pl lm) ∧ StkApart s'.mem st bp (8 * NB pl lm) ∧
      StkAfter R L L' st (stLen s.mem st) pl lm s.mem s'.mem ∧
      MemFrame s.mem s'.mem (AW R kc s pw pl st) ∧ LiveFrame s.mem s'.mem L (LW s pw pl st)

/-- the goal of every segment -/
@[reducible] def GoalQ (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) : State → Prop := fun s' =>
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    Post R kc sqC mlC b L st pw pl lm x xl s s'

@[reducible] def Goal (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat)
    (mlC : Nat → Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s S : State) : Prop :=
  ReachesRet (LibExp.program.link impl) (s.regs 30) S (GoalQ R kc sqC mlC b L st pw pl lm x xl s)

/-- the frame slots of the function (from the entry `sp`; `+56 … +72`: the spilled `x` header, entry `X6 … X8`) -/
@[reducible] def Sl (s : State) (st pw pl lm : Nat) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat ∧ M.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat ∧
    M.readLE (s.sp.toNat + 8) 8 = st ∧ M.readLE (s.sp.toNat + 16) 8 = pw ∧ M.readLE (s.sp.toNat + 24) 8 = pl ∧
    M.readLE (s.sp.toNat + 48) 8 = lm ∧ M.readLE (s.sp.toNat - 64) 8 = W lm ∧
    M.readLE (s.sp.toNat - 56) 8 = lm + 63 ∧ M.readLE (s.sp.toNat - 48) 8 = pl ∧
    M.readLE (s.sp.toNat + 56) 8 = (s.regs 6).toNat ∧ M.readLE (s.sp.toNat + 64) 8 = (s.regs 7).toNat ∧
    M.readLE (s.sp.toNat + 72) 8 = (s.regs 8).toNat

/-- the facts that hold at every point after `stk.nat` (memory `M`, live set `L1`, budget `b1`) -/
structure Ctx (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm : Nat) (s : State) (bp : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  fr : MemFrame s.mem M (AW R kc s pw pl st)
  lf : LiveFrame s.mem M L (LW s pw pl st)
  rg : M.regions = s.mem.regions
  le : LiveExt R L L1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M)
  scr : Scr R L L1 s.mem M st bp (NB pl lm)
  sa : StkAfter R L L1 st (stLen s.mem st) pl lm s.mem M
  sap : StkApart M st bp (8 * NB pl lm)
  sl : Sl s st pw pl lm M

end FvModexp.Arm64.P2Pre
