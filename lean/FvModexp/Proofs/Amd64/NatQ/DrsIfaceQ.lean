import FvModexp.Proofs.Amd64.Nat.DivLargeDefs
import FvModexp.Proofs.Amd64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# `divRecursiveStep`'s statement, Q-form (TIGHT COSTS, amd64; owner asm): `Q.DivLarge.DrsPreW` / `DrsPostW` / `DrsHypQ`

Twins of top's `Amd64/Nat/DivLargeDefs.lean` `DrsPreW` / `DrsPostW` / `DrsHyp` (same conjunct order and accessors'
meaning), with the arm64 Q changes (Arm64/NatQ/DrsIfaceQ.lean): a reserve level `H` and a LEVEL-FREE consumption `cost`
(e.g. `Q.drsCQ ul vl`); the pre's cost slot is `(stLen + 12·vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b)`, the post's
`RtPost … cost` is `RtPostQ … (cost + stkR H s.mem st) (stkR H s'.mem st)`. Args `RAX, RBX, RCX = z (q)`, `RDI = stk`,
`RSI, R8, R9 = u`, `R10 = depth`, `v = (vp, vl, vc)` on the stack at `RSP + 8, + 16, + 24` (Nat, bound by `vpS/vlS/vcS`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge (StkIn drsFn drsNames)

/-- the Q precondition of `divRecursiveStep` with the stack window `W` (conjunct order as `DivLarge.DrsPreW`; the
`cost` conjunct is the pair `(stLen + 12·vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b)`) -/
def DrsPreW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  (CallEnv R L s W 96) ∧
  (Serves R) ∧
  (RunIface.Globals R s.mem (win s W 96)) ∧
  (ql ≤ qc) ∧
  (qc < 2 ^ 40) ∧
  (ul ≤ uc) ∧
  (uc < 2 ^ 40) ∧
  (vl ≤ vc) ∧
  (vc < 2 ^ 40) ∧
  (2 ≤ vl) ∧
  (vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9) ∧
  (2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) ∧
  (natVal s.mem qp ql = 0) ∧
  (2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql))) ∧
  (s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧ Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧ Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧ Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48) ∧
  (Apart qp (8 * ql) up (8 * ul)) ∧
  (Apart qp (8 * ql) vp (8 * vl)) ∧
  (Apart up (8 * ul) vp (8 * vl)) ∧
  (StkIn R L s W 96 st) ∧
  (stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧ Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧ (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0)) ∧
  (Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96)) ∧
  (Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  (stLen s.mem st + 12 * vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl) ∧
  (s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc) ∧
  (Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 ∧ Apart up (8 * ul) (s.fsBase.toNat - 8) 8 ∧ Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8)

/-- the Q precondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  DrsPreW R b L H cost 40960 qp ql qc st up ul uc vp vl vc s

/-- the Q postcondition of `divRecursiveStep` with the stack window `W` (FS base and DF kept) -/
@[reducible] def DrsPostW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl ∧
  natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), RtPostQ R b (cost + stkR H s.mem st) (stkR H s'.mem st) L L' b' s s' ∧
    StackBackL R L L' st s.mem s'.mem ∧
    MemFrame s.mem s'.mem (R.rt ++ win s W 96 ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st)

/-- the Q postcondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  DrsPostW R b L H cost 40960 qp ql st up ul vp vl s s'

/-- **`divRecursiveStep`'s `Ensures`, Q-form** (amd64; on the division library program `LibDrs`; `dc ul vl` level-free;
`v`'s words bound by the pre's stack slots) -/
def DrsHypQ (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat),
    Ensures ((Extracted.program.onlySegments drsNames).link impl) (segAddr Extracted.program drsFn)
      [qp, ql, qc, st, up, ul, uc, d]
      (fun s => DrsPre R b L H (dc ul.toNat vl) qp.toNat ql.toNat qc.toNat st.toNat up.toNat ul.toNat uc.toNat
        vp vl vc s)
      (fun s s' => DrsPost R b L H (dc ul.toNat vl) qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl s s')

end FvModexp.Amd64.Q.DivLarge
