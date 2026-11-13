import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Amd64.NatQ.SqrDefs
import FvModexp.Proofs.Amd64.NatQ.MulHypQE
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs
import FvModexp.Proofs.Amd64.Nat.TruncDefs
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (go-bigmodexpfix nat.go:856-899), amd64 — statement pieces (agent divmc s61;
twin of infra's `FvModexp.Arm64.P2Pre` (Arm64/Exp/P2PreDefs), Q-form callees from the start)

ABIInternal: `stk` RAX, `powers` (RBX, RCX, RDI), `windowSize` RSI, `logM` R8, `x` (R9, R10, R11). Entry `0x5e8900`.
Frame: `PUSHQ BP` (saved `RBP` at `RSP - 8`), `SUBQ $0xa8, SP` (`SP' = RSP - 176`, `RBP' = RSP - 8`); spills `stk`
`0xb8(SP') = RSP + 8`, `powers.ptr` `RSP + 16`, `logM` `RSP + 48`, `x` `RSP + 56 … + 72` (`above = 80`); locals
`1 << windowSize` `RSP - 32`, `len(powers)` `RSP - 40`, `w = ⌈logM/64⌉` `RSP - 48`, loop `i` `RSP - 56`, `3 i` `RSP - 64`.
Callees (`stk.nat`, `trunc`, `sqr`, `mul`, `memmove`, `gcWriteBarrier2`) run with `RSP_c = RSP - 184`; `mul`'s `y` is
passed at `RSP_c + 8 … + 24`; the deepest callee window is `kc` → `K kc = 184 + kc`. Callee `above` areas end at
`RSP_c + 88 = RSP - 96` at most, below every local live across a call.

Same restrictions as arm64 (callers `expNNPowerOfTwoWindowSize{2,4}`): `windowSize ∈ {2, 4}`, `len = 2^windowSize`,
`2 ≤ logM ≤ 2^13`, `x` normalised, a non-nil `stk`, `powers` a caller-frame array outside the runtime. amd64-specific:
the stack object's facts are divmc's `Q.NatSqr.StkPre` (guard word, TLS slot, `runtime.writeBarrier`, the threshold
globals), `x`/`natOne`/`powers` `StkSep`, `powers` apart from the TLS slot and the guard word, `hasADX` readable
(`sqr`/`mul` read it). The internal `Pre` ends with `[RSP] < 2^47` (callers re-derive it from `CallSetup.ret`).
Callees as premises: `SqrE`/`Q.DivRec.MulHypQE` (= divmc's `Q.NatSqr.ens` / `Q.NatMul.ens` shapes on a program `ns`),
`StackNatX.HypQ`, `Trunc.Hyp2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.buildPrecomputationWindowModPower2"

theorem fnBase : segAddr LibW.program fn = 0x5e8900 := by decide

/-- **`nat.sqr` as a callee, Q-form** (amd64; program `ns`, callee window `W`): divmc's `Q.NatSqr.ens` shape -/
def SqrE (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (W : Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program Q.NatSqr.fn)
      [zp, zl, zc, st, xp, xl, xc]
      (Q.NatSqr.SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)
      (Q.NatSqr.SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)

/-- bytes above `RSP` (return address + the 9 argument spill words) -/
abbrev A : Nat := 80

/-- stack bytes below `RSP`: the frame (176), the callee's return-address slot (8), the deepest callee window `kc` -/
@[reducible] def K (kc : Nat) : Nat := 184 + kc

/-- `w = ⌈logM / 64⌉` (nat.go:860) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the words of `buf` -/
@[reducible] def NB (pl lm : Nat) : Nat := (pl + 1) * W lm

/-- a `trunc` budget (any result length `≤ w`) -/
@[reducible] def tC (lm : Nat) : Nat := makeCost (W lm + 4)

/-- one loop round: `sqr`, `mul`, two `trunc`s (divmc's Q-form costs at the largest operand length `w`) -/
@[reducible] def rc (lm : Nat) : Nat := sqrCQ (W lm) + mulCQ (W lm) (W lm) + 2 * tC lm

/-- the budget: `trunc(x)` before the loop (`stk.nat` is paid by the stack reserve), `len/2 - 1` rounds -/
@[reducible] def cost (pl lm : Nat) : Nat := tC lm + (pl / 2 - 1) * rc lm

/-- the stack reserve span of the function: `buf` (`rnd NB`) + the loop's `sqr`/`mul` scratch (`8 w + 64`) -/
@[reducible] def DPre (pl lm : Nat) : Nat := StackNat.rnd (NB pl lm) + 8 * W lm + 64

/-- the reserve level for an entry stack length `ℓ` -/
@[reducible] def HP (l pl lm : Nat) : Nat := l + DPre pl lm

/-- the ranges the function writes (besides the runtime's and the window) -/
@[reducible] def LW (s : State) (pw pl st : Nat) : List (Nat × Nat) := [(pw, pw + 24 * pl)] ++ stkWs s.mem st

@[reducible] def AW (R : RtInv) (kc : Nat) (s : State) (pw pl st : Nat) : List (Nat × Nat) :=
  R.rt ++ win s (K kc) A ++ LW s pw pl st

/-- **the internal pre** (effective budget `b`, the invariant at `b + stkR (HP …)`), ending with the return-address
fact and the ABI entry facts `X15 = 0`, `DF = 0` (from `CallSetup`) -/
@[reducible] def Pre (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl ws lm x xl : Nat) (s : State) :
    Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧ Globals R s.mem (win s (K kc) A ++ [(pw, pw + 24 * pl), (st, st + 24)]) ∧
    (ws = 2 ∨ ws = 4) ∧ pl = 2 ^ ws ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧
    pw % 8 = 0 ∧ pw + 24 * pl ≤ 2 ^ 48 ∧ s.mem.accessible pw (24 * pl) true = true ∧ Outside pw (24 * pl) R.rt ∧
    Outside pw (24 * pl) (win s (K kc) A) ∧ Apart pw (24 * pl) (guard s) 8 ∧ Apart pw (24 * pl) (tls s) 8 ∧
    StkSep s.mem st pw (24 * pl) ∧ (0 < xl → Apart pw (24 * pl) x (8 * xl)) ∧
    RdIn R L s (K kc) A x xl ∧ NatNorm s.mem x xl ∧ xl ≤ 2 ^ 12 ∧ (0 < xl → StkSep s.mem st x (8 * xl)) ∧
    StkPre R L s (K kc) A st ∧ stLen s.mem st + 2 ^ 12 ≤ 2 ^ 16 ∧
    (∃ op, NatOne R L s.mem op (win s (K kc) A ++ LW s pw pl st) ∧ StkSep s.mem st op 8) ∧
    cost pl lm ≤ b ∧ R.inv (b + stkR (HP (stLen s.mem st) pl lm) s.mem st) L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Outside NatAdd.wordT 16 R.rt ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0 ∧ s.df = false

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
@[reducible] def StkAfter (R : RtInv) (L L' : List (Nat × Nat)) (st l pl lm : Nat) (m0 m : Memory) : Prop :=
  StkOK m R L' st ∧ stLen m st = l + StackNat.rnd (NB pl lm) ∧
    ((stW m st = stW m0 st ∧ stCap m st = stCap m0 st) ∨
      (InRanges (stW m st) (8 * stCap m st) R.rt ∧ ApartAll (stW m st) (8 * stCap m st) L))

/-- `buf` (`[bp, bp + n)`) lies in the stack's current array below its level, or apart from the array -/
@[reducible] def BU (M : Memory) (st bp n : Nat) : Prop :=
  (stW M st ≤ bp ∧ bp + n ≤ stW M st + 8 * stLen M st) ∨ Apart bp n (stW M st) (8 * stCap M st)

/-- the result facts (effective budget form) -/
@[reducible] def Post (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ bp : Nat, (∀ j, j < pl → PwD s'.mem pw bp lm (natVal s.mem x xl) j) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - cost pl lm + stkR (HP (stLen s.mem st) pl lm) s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      Scr R L L' s.mem s'.mem st bp (NB pl lm) ∧ StkSep s'.mem st bp (8 * NB pl lm) ∧
      StkAfter R L L' st (stLen s.mem st) pl lm s.mem s'.mem ∧
      MemFrame s.mem s'.mem (AW R kc s pw pl st) ∧ LiveFrame s.mem s'.mem L (LW s pw pl st) ∧
      ArrIn L' st s.mem s'.mem ∧ BU s'.mem st bp (8 * NB pl lm)

/-- the registers every path keeps (`RSP` popped past the return address, `RBP`, `g`, `X15`) and `Post` -/
@[reducible] def GoalQ (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) :
    State → Prop := fun s' =>
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    Post R kc b L st pw pl lm x xl s s'

/-- what the function promises, from a state `S` inside its frame (entry state `s`) -/
@[reducible] def Goal (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl lm x xl : Nat) (s S : State) : Prop :=
  ReachesRet (LibW.program.link impl) (retAddrOf s) S (GoalQ R kc b L st pw pl lm x xl s)

/-- the ABIInternal state facts every segment carries (`g`, TLS base, `X15`, `DF`) -/
@[reducible] def Abi (s S : State) : Prop :=
  S.regs 14 = s.regs 14 ∧ S.fsBase = s.fsBase ∧ S.xmm 15 = s.xmm 15 ∧ S.df = s.df

/-- the frame slots (from the entry `RSP`): return address, saved `RBP`, the spills and the three locals written at the
entry (`1 << ws`, `len`, `w`) -/
@[reducible] def Sl (s : State) (st pw pl lm x xl : Nat) (M : Memory) : Prop :=
  M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧ M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    M.readLE ((s.regs 4).toNat + 8) 8 = st ∧ M.readLE ((s.regs 4).toNat + 16) 8 = pw ∧
    M.readLE ((s.regs 4).toNat + 48) 8 = lm ∧ M.readLE ((s.regs 4).toNat + 56) 8 = x ∧
    M.readLE ((s.regs 4).toNat + 64) 8 = xl ∧ M.readLE ((s.regs 4).toNat + 72) 8 = (s.regs 11).toNat ∧
    M.readLE ((s.regs 4).toNat - 32) 8 = pl ∧ M.readLE ((s.regs 4).toNat - 40) 8 = pl ∧
    M.readLE ((s.regs 4).toNat - 48) 8 = W lm

/-- the facts that hold at every point after `stk.nat` (memory `M`, live set `L1`, effective budget `b1`) -/
structure Ctx (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (bp : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  fr : MemFrame s.mem M (AW R kc s pw pl st)
  lf : LiveFrame s.mem M L (LW s pw pl st)
  rg : M.regions = s.mem.regions
  le : LiveExt R L L1
  inv : R.inv (b1 + stkR (HP (stLen s.mem st) pl lm) M st) L1 (s.regs 14).toNat (view R.rt L1 M)
  scr : Scr R L L1 s.mem M st bp (NB pl lm)
  sa : StkAfter R L L1 st (stLen s.mem st) pl lm s.mem M
  sap : StkSep M st bp (8 * NB pl lm)
  sl : Sl s st pw pl lm x xl M
  ain : ArrIn L1 st s.mem M
  bu : BU M st bp (8 * NB pl lm)

end FvModexp.Amd64.P2Pre
