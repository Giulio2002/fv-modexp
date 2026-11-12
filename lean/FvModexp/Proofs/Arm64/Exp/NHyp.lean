import FvModexp.Proofs.Arm64.Exp.ExpHyp
import FvModexp.Proofs.Arm64.Exp.MulHyp
import FvModexp.Proofs.Arm64.Nat.StackNatCall

set_option autoImplicit false

/-!
# Callee premises of `nat.expNN` (arm64): `nat.rem` (asm), `nat.expNNSlow` / `nat.expNNPowerOfTwo` (infra)

Hypotheses (ExpHyp style, CONVENTIONS §3) until the owners land their summaries. All three take a stack `st` and write a
result nat into `z` (`X0..X2`) or a fresh array; they share one entry shape `CPre` and one exit shape `CPost`:

* `CPre … zp zl zc st ins need cst s`: the call environment of the window `win s stk above` (+ `Serves`, `Globals`), `z`
  written (`WrOut`, `zl ≤ zc`), every input `(p, n) ∈ ins` read (`RdIn`, `n ≤ 2^9`, normalised) and apart from `z`, the
  stack header and the stack's free part; the stack (`StkOK`, header/array outside the window, array apart from the
  guard word, `stCap = 0 → stW = 0`, `stLen + need ≤ 2^16`); the write-barrier flag readable and apart from the header;
  the written ranges (`z`, header, free part) apart from the threshold globals `gA` (as `ExpHyp.DivPre`); `cst ≤ b`.
* `CPost … zp zc st v cst s s'`: result `(p, l, c)` in `X0..X2` with value `v` (pre-state values), normalised, old or
  fresh (`ExpHyp.NatOF … 1`), `RtPost`, `StackBackL` (the stack array, when not the entry one, is an element of `L'`),
  frame `R.rt ++ winA ++ [z] ++ stkWs`, `LiveFrame L ([z] ++ stkWs)`.

Values: `rem` → `U % V`; `expNNSlow` → `X ^ Y % M` (`0 < X`, `2 ≤ Y`, `0 < M`; `Exp.expNNSlow_correct` bridges the model);
`expNNPowerOfTwo` → `X ^ Y % 2 ^ logM` (`0 < X`, `0 < Y`, `1 ≤ logM ≤ 2^13`). Costs/needs are parameters (functions of
the stack length and the operand word counts), as `ExpHyp.DivHyp`'s `cost`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NHyp

open FvModexp.Arm64.ExpHyp

/-- the free part of the stack `(start, bytes)` -/
@[reducible] def freeOf (m : Memory) (st : Nat) : Nat × Nat :=
  (stW m st + 8 * stLen m st, 8 * (stCap m st - stLen m st))

/-- common entry facts of a stack-taking callee of `nat.expNN` -/
@[reducible] def CPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st : Nat)
    (ins : List (Nat × Nat)) (need cst : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ RoOut R ∧
    Outside StackNat.wT 16 R.rt ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    (∀ p n, (p, n) ∈ ins → RdIn R L s stk above p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧ (0 < zc → Apart zp (8 * zc) p (8 * n))) ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧ Apart st 24 ((s.regs 28).toNat + 16) 8 ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    (stCap s.mem st = 0 → stW s.mem st = 0) ∧ stLen s.mem st + need ≤ 2 ^ 16 ∧
    s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
    (0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
      Apart zp (8 * zc) RunIface.gA 32) ∧
    Apart st 24 RunIface.gA 32 ∧ Apart (freeOf s.mem st).1 (freeOf s.mem st).2 RunIface.gA 32 ∧
    cst ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- common exit facts: the result nat `(p, l, c)` (`X0..X2`) of value `v` -/
@[reducible] def CPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF R L L' s'.mem zp zc 1 p l c v ∧ RtPost R b cst L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

/-- `CPost` with `ResSep` (coordinator decision on "[expmc s26] ResSep"): the callee shape of `rem`/`expNNSlow`/
`expNNPowerOfTwo` (a non-empty result is apart from the stack's final array when that array is not the entry one) -/
@[reducible] def CPostR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF R L L' s'.mem zp zc 1 p l c v ∧ RtPost R b cst L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-! ## `z.rem(stk, u, v)` (natdiv.go:505) — z X0..X2, st X3, u X4..X6, v X7..X9; result `U % V` -/

def fnRem : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem"

/-- `¬alias(z, u)` (nat.go `alias`: the addresses of the last cap words differ, as 64-bit machine addresses) — `rem`'s
extra pre conjunct (coordinator DECISIONS 2026-11-13 on "[asm s31] FINDING"; = asm's `NatRem.NoAlias`) -/
@[reducible] def NoAlias (zp zc up uc : Nat) : Prop :=
  0 < zc → 0 < uc → (zp + 8 * (zc - 1)) % 2 ^ 64 ≠ (up + 8 * (uc - 1)) % 2 ^ 64

def RemHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnRem)
      [z, zl, zc, st, u, ul, uc, v, vl, vc]
      (fun s => (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(u.toNat, ul.toNat), (v.toNat, vl.toNat)]
          (need ul.toNat vl.toNat) (cost (stLen s.mem st.toNat) ul.toNat vl.toNat) s ∧
        0 < vl.toNat) ∧ NoAlias z.toNat zc.toNat u.toNat uc.toNat)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v.toNat vl.toNat)
        (cost (stLen s.mem st.toNat) ul.toNat vl.toNat) s s')

/-! ## `z.expNNSlow(stk, x, y, m)` (nat.go:732) — z X0..X2, st X3, x X4..X6, y X7..X9, m X10..X12; `X ^ Y % M` -/

def fnSlow : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNSlow"

def SlowHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSlow)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]
      (fun s => CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat
          [(x.toNat, xl.toNat), (y.toNat, yl.toNat), (m.toNat, ml.toNat)]
          (need xl.toNat yl.toNat ml.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl.toNat ml.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 2 ≤ natVal s.mem y.toNat yl.toNat ∧ 0 < natVal s.mem m.toNat ml.toNat ∧
        0 < st.toNat)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y.toNat yl.toNat % natVal s.mem m.toNat ml.toNat)
        (cost (stLen s.mem st.toNat) xl.toNat yl.toNat ml.toNat) s s')

/-! ## `z.expNNPowerOfTwo(stk, x, y, logM)` (nat.go:906) — z X0..X2, st X3, x X4..X6, y X7..X9, logM X10;
`X ^ Y % 2 ^ logM`. Pre's last conjunct (infra s18 request): the package global `natOne` (`powers[0].set(natOne)` in
`buildPrecomputationWindowModPower2`), outside the window, `z` and the stack's written ranges, apart from the stack. -/

def fnP2 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwo"

def P2Hyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc lm : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnP2)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, lm]
      (fun s => CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y.toNat, yl.toNat)]
          (need xl.toNat yl.toNat lm.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl.toNat lm.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 0 < natVal s.mem y.toNat yl.toNat ∧ 1 ≤ lm.toNat ∧ lm.toNat ≤ 2 ^ 13 ∧ 0 < st.toNat ∧
        ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(z.toNat, z.toNat + 8 * zc.toNat)] ++ stWs s.mem st.toNat) ∧
          EvenHyp.StkApart s.mem st.toNat op 8)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y.toNat yl.toNat % 2 ^ lm.toNat)
        (cost (stLen s.mem st.toNat) xl.toNat yl.toNat lm.toNat) s s')

end FvModexp.Arm64.NHyp
