import FvModexp.Proofs.Arm64.Nat.LibDrs
import FvModexp.Proofs.Arm64.Exp.MulHyp
import FvModexp.Proofs.Arm64.Nat.DivBasicDefs
import FvModexp.Proofs.Common.DivmcLsl
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `divRecursiveStep`'s statement as `divLarge` calls it (arm64): `DrsPreW` / `DrsPostW` / `DrsHyp`

Split out of `DivLargeDefs` (asm s37) so that the drs proof chain does not import `LibDivL` (the divLarge program);
(asm s42: nor `Nat.DivBasic` — the Q drs chain imports this module; importers that need divBasic import it themselves);
`DivLargeDefs` imports this module, so every name stays `FvModexp.Arm64.DivLarge.*`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.DivLarge

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge"
def drsFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep"
/-- the program of `divRecursiveStep`'s statement: the division tree without `divLarge` (and `nat.div`) -/
def drsNames : List String := LibDrs.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-! ## `divRecursiveStep` (natdiv.go:750) — the callee's statement (proved in DivRec*.lean)

Args `X0..X2 = z (q)`, `X3 = stk`, `X4..X6 = u`, `X7..X9 = v`, `X10 = depth`. Value contract = mathdiv's `Mdl.RecOk`
(Common/DivRecCore.lean): `z` all zero, `v` with its top bit set, `2·U < 2^(64·(len v + len z))` → `z = U / V`,
`u = U mod V` in place. Window `40960 / 96`; `dc ℓ ul vl` is the budget bound (`ℓ` the stack length at entry). -/

/-- the precondition of `divRecursiveStep` with the stack window `W` (the induction runs one frame down per level) -/
def DrsPreW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost W : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  CallEnv R L s W 96 ∧ Serves R ∧ RunIface.Globals R s.mem (win s W 96) ∧
  ql ≤ qc ∧ qc < 2 ^ 40 ∧ ul ≤ uc ∧ uc < 2 ^ 40 ∧ vl ≤ vc ∧ vc < 2 ^ 40 ∧
  2 ≤ vl ∧ (vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9) ∧ 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 ∧
  natVal s.mem qp ql = 0 ∧ 2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql)) ∧
  (s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧
    Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 28).toNat + 16) 8) ∧
  (s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧
    Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 28).toNat + 16) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧
    Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48) ∧
  Apart qp (8 * ql) up (8 * ul) ∧ Apart qp (8 * ql) vp (8 * vl) ∧ Apart up (8 * ul) vp (8 * vl) ∧
  EvenHyp.StkIn R L s W 96 st ∧ (stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧
    Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0)) ∧
  (Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
  Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96) ∧
  (Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  cost ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- the precondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  DrsPreW R b L cost 40960 qp ql qc st up ul uc vp vl vc s

/-- the postcondition of `divRecursiveStep` with the stack window `W` -/
@[reducible] def DrsPostW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost W : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl ∧
  natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), ExpHyp.RtPost R b cost L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
    MemFrame s.mem s'.mem (R.rt ++ winA s W 96 ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st)

/-- the postcondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  DrsPostW R b L cost 40960 qp ql st up ul vp vl s s'

/-- `divRecursiveStep`'s `Ensures` (on the division library program) -/
def DrsHyp (impl : List Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc d : BitVec 64),
    Ensures ((Extracted.program.onlySegments drsNames).link impl) (segAddr Extracted.program drsFn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc, d]
      (fun s => DrsPre R b L (dc (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat st.toNat up.toNat
        ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s)
      (fun s s' => DrsPost R b L (dc (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat st.toNat up.toNat
        ul.toNat vp.toNat vl.toNat s s')

/-! ## `divLarge` -/

end FvModexp.Arm64.DivLarge
