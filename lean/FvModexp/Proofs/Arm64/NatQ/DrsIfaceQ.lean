import FvModexp.Proofs.Arm64.Nat.DrsIface
import FvModexp.Proofs.Arm64.Nat.RtPostQ

set_option autoImplicit false

/-!
# `divRecursiveStep`'s statement, Q-form (TIGHT COSTS, asm s38): `Q.DivLarge.DrsPreW` / `DrsPostW` / `DrsHypQ`

Twins of Arm64/Nat/DrsIface.lean with a reserve level `H` and a LEVEL-FREE consumption `cost` (e.g. `Q.drsCQ ul vl`):
the pre's cost slot is `(stLen + 12·vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b)` (the level twin of the `2 ^ 16` bound),
the post's `RtPost … cost` is `RtPostQ … (cost + stkR H s.mem st) (stkR H s'.mem st)`. Everything else verbatim.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge

/-- the precondition of `divRecursiveStep` with the stack window `W` (the induction runs one frame down per level) -/
def DrsPreW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
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
  (stLen s.mem st + 12 * vl + 64 ≤ H ∧ cost + stkR H s.mem st ≤ b) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- the precondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  DrsPreW R b L H cost 40960 qp ql qc st up ul uc vp vl vc s

/-- the postcondition of `divRecursiveStep` with the stack window `W` -/
@[reducible] def DrsPostW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost W : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl ∧
  natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), RtPostQ R b (cost + stkR H s.mem st) (stkR H s'.mem st) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
    MemFrame s.mem s'.mem (R.rt ++ winA s W 96 ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st)

/-- the postcondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H cost : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  DrsPostW R b L H cost 40960 qp ql st up ul vp vl s s'

/-- **`divRecursiveStep`'s `Ensures`, Q-form** (on the division library program; `dc ul vl` level-free) -/
def DrsHypQ (impl : List Segment) (R : RtInv) (dc : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc d : BitVec 64),
    Ensures ((Extracted.program.onlySegments drsNames).link impl) (segAddr Extracted.program drsFn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc, d]
      (fun s => DrsPre R b L H (dc ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat st.toNat up.toNat ul.toNat uc.toNat
        vp.toNat vl.toNat vc.toNat s)
      (fun s s' => DrsPost R b L H (dc ul.toNat vl.toNat) qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp.toNat vl.toNat
        s s')

end FvModexp.Arm64.Q.DivLarge
