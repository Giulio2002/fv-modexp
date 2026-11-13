import FvModexp.Proofs.Arm64.Nat.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.MulHypQE
import FvModexp.Proofs.Arm64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# `divRecursiveStep` (arm64), Q-form (TIGHT COSTS, asm s38): the recursion family

Twin of the second half of Arm64/Nat/DrsDefs.lean: `Args` gains the reserve level `Hq` (FIXED along the recursion: the
inner call is made with the caller's `Hq`), `preOf`/`postOf` use the Q-form `DrsPreW`/`DrsPostW` (DrsIfaceQ) with the
level-free budget `Q.drsCQ` (DivHypQ). The window (`drsW`), `fn`/`names` and the old budget are the original's (opened);
the `nat.mul` premise is `Q.DivRec.MulHypQE` (MulHypQE.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec
open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-! ## The recursion as one family of summaries -/

/-- a call: budget, live set, window and the eleven argument registers `z = (qp, ql, qc)`, `stk`, `u = (up, ul, uc)`,
`v = (vp, vl, vc)`, `depth` -/
structure Args where
  Hq : Nat
  b : Nat
  L : List (Nat × Nat)
  W : Nat
  qp : BitVec 64
  ql : BitVec 64
  qc : BitVec 64
  st : BitVec 64
  up : BitVec 64
  ul : BitVec 64
  uc : BitVec 64
  vp : BitVec 64
  vl : BitVec 64
  vc : BitVec 64
  d : BitVec 64

/-- the argument registers and the return-address facts at the entry -/
@[reducible] def Entry (a : Args) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = a.qp ∧ s.regs 1 = a.ql ∧ s.regs 2 = a.qc ∧
    s.regs 3 = a.st ∧ s.regs 4 = a.up ∧ s.regs 5 = a.ul ∧ s.regs 6 = a.uc ∧ s.regs 7 = a.vp ∧ s.regs 8 = a.vl ∧
    s.regs 9 = a.vc ∧ s.regs 10 = a.d

/-- the member precondition: window large enough, `DrsPreW` (Q-form, level `a.Hq`) with the budget `drsCQ` -/
def preOf (R : RtInv) (a : Args) (s : State) : Prop :=
  Entry a s ∧ drsW a.vl.toNat ≤ a.W ∧
    DrsPreW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl.toNat) a.W a.qp.toNat a.ql.toNat a.qc.toNat
      a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat s

/-- the callee-saved part of the post -/
@[reducible] def Kept (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18

def postOf (R : RtInv) (a : Args) (s s' : State) : Prop :=
  Kept s s' ∧ DrsPostW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl.toNat) a.W a.qp.toNat a.ql.toNat
    a.st.toNat a.up.toNat a.ul.toNat a.vp.toNat a.vl.toNat s s'

/-- the measure: the divisor length -/
def μ (a : Args) (_ : State) : Nat := a.vl.toNat

/-- the program of the summary -/
abbrev P (impl : List Segment) : Program := LibDrs.program.link impl

/-- the induction hypothesis below measure `n` -/
@[reducible] def IH (impl : List Segment) (R : RtInv) (n : Nat) (a : Args) : Prop :=
  Summary (P impl) 0x1ba3a0 (fun s => preOf R a s ∧ μ a s < n) (postOf R a)

end FvModexp.Arm64.Q.DivRec
