import FvModexp.Proofs.Amd64.Exp.NHyp

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.ExpHyp (stWs)

/-- `P2Hyp`'s precondition as a named predicate (definitionally the lambda of `P2Hyp`; top s53, for the Janus v0.4.0 `hinv`
lemmas `P2DEInv*`). -/
@[reducible] def P2PreS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) (z zl zc st x xl xc lm : BitVec 64) (y yl yc : Nat)
    (s : State) : Prop :=
  StkArg s 0 y yl yc ∧
        (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y, yl)]
          (need xl.toNat yl lm.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl lm.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 0 < natVal s.mem y yl ∧ 1 ≤ lm.toNat ∧ lm.toNat ≤ 2 ^ 13 ∧
        0 < st.toNat ∧
        ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(z.toNat, z.toNat + 8 * zc.toNat)] ++
            stWs s.mem st.toNat) ∧ StkApart s.mem st.toNat op 8) ∧ xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40 ∧
        XGc s.mem st.toNat x.toNat xl.toNat xc.toNat

end FvModexp.Amd64.NHyp
