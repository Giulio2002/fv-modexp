import FvModexp.Proofs.Arm64.NatQ.DivRel
import FvModexp.Proofs.Arm64.Nat.DivW0
import FvModexp.Proofs.Arm64.Exp.RdIn0

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivMBase.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `z = nil` / `stk == nil` forms: the parts that do not mention `IMod` (`costM`, `PFM`, `wsum0`)

Split out of `DivMDefs` (asm s37) so that `nat.div`'s `DivHypLG` modules (DivZOne/DivZTwo/DivMOneA, in DivRow's
closure) do not import `Int.ModDefs` / `LibMod`; `DivMDefs` imports this module (names unchanged).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

/-- the budget of the `stk == nil` form -/
@[reducible] def costM (dc : Nat → Nat → Nat) (ul vl : Nat) : Nat := costMQ dc ul vl

/-- `IMod.DivPreM`'s conjuncts by name -/
structure PFM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s : State) : Prop where
  ce : CallEnv R L s 41504 112
  sv : RunIface.Serves R
  gl : RunIface.Globals R s.mem (win s 41504 112)
  ulc : ul ≤ uc
  uo : ExpHyp.WrOut R L s 41504 112 u uc
  ui : ExpHyp.RdIn0 R L s 41504 112 u ul
  vo : ExpHyp.RdIn R L s 41504 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  ug : 0 < uc → Apart u (8 * uc) v (8 * vl) ∧ Apart u (8 * uc) RunIface.gA 32
  pg : RunIface.PoolG R s.mem (win s 41504 112)
  cost : costM dc ul vl ≤ b
  inv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- `ul > 0` ⇒ `uc > 0` and `u` is a readable input -/
theorem PFM.uin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl : Nat}
    {s : State} (hp : PFM R b dc L u ul uc v vl s) (hu : 0 < ul) : ExpHyp.RdIn R L s 41504 112 u ul :=
  hp.ui.2 hu

set_option linter.defProp false in
/-- `nat.divW` (`DivW.ens0`, possibly-nil empty dividend) as a summary in `LibDiv.program.link impl` -/
def wsum0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :=
  Ensures.toSummaryIn (DivW.ens0 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) (noExit_restrict hap DivW.names)
    (show CodeIn ((Extracted.program.onlySegments DivW.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide)))

end FvModexp.Arm64.Q.NatDiv
