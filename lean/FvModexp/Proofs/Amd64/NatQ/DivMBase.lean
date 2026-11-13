import FvModexp.Proofs.Amd64.NatQ.DivRel
import FvModexp.Proofs.Amd64.Exp.RdIn0

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil` form (`IMod.DivHypM`), Q-form: the parts that do not mention `IMod` (top s39)

Twin of Arm64/NatQ/DivMBase.lean + the `costMQ`/`HM` definitions of Arm64/NatQ/DivHypQ.lean (asm's amd64 NatQ/DivHypQ
has no `stk == nil` cost): `HM ul = 16·ul + 64` (`getStack()` returns `len = 0`), `costMQ dc = costQ dc + stkRes HM + 24`
(the plain form `C + stkRes H` + the 24-byte `newobject` of `getStack`), `PFM` = `IMod.DivPreM`'s conjuncts by name
(amd64: the six stack words first). `wsum0` (DivZOne) is shared with the stack-given form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv

/-- the reserve level of the `stk == nil` form (`getStack()` returns `len = 0`; `nat.div`'s bound `16·len u + 64`) -/
@[reducible] def HM (ul : Nat) : Nat := 16 * ul + 64

/-- the budget of the `stk == nil` form (`IMod.DivHypM`'s cost argument) -/
@[reducible] def costMQ (dc : Nat → Nat → Nat) (ul vl : Nat) : Nat := costQ dc ul vl + stkRes (HM ul) + 24

/-- `IMod.DivPreM`'s conjuncts by name -/
structure PFM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl vc : Nat) (s : State) : Prop where
  su : s.mem.readLE ((s.regs 4).toNat + 8) 8 = u
  sul : s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul
  suc : s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc
  sv : s.mem.readLE ((s.regs 4).toNat + 32) 8 = v
  svl : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl
  svc : s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc
  ce : CallEnv R L s 41512 112
  srv : RunIface.Serves R
  gl : RunIface.Globals R s.mem (win s 41512 112)
  ulc : ul ≤ uc
  uo : EvenHyp.WrOut R L s 41512 112 u uc
  ui : EvenHyp.RdIn0 R L s 41512 112 u ul
  vo : EvenHyp.RdIn R L s 41512 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  ug : 0 < uc → Apart u (8 * uc) v (8 * vl) ∧ Apart u (8 * uc) RunIface.gA 32
  pg : RunIface.PoolG R s.mem (win s 41512 112)
  cost : costMQ dc ul vl ≤ b
  inv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- `ul > 0` ⇒ `u` is a readable input -/
theorem PFM.uin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat}
    {s : State} (hp : PFM R b dc L u ul uc v vl vc s) (hu : 0 < ul) : EvenHyp.RdIn R L s 41512 112 u ul :=
  hp.ui.2 hu

end FvModexp.Amd64.Q.NatDiv
