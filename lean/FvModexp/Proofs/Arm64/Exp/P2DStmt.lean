import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the callee shape `P2HypC` (agent infra, s39)

`NHyp.P2Hyp` plus the pre conjunct `len x ≤ cap x < 2^40` (NOTES-conventions "[infra s39] FINDING"): the even-base path
runs `nat(nil).rsh(x, i)`, whose `x[m-n:]` slice keeps the pointer offset only when `cap x − (m − n) ≠ 0`; with an
unconstrained `cap x` register the statement is false. Kept in its own module (REBUILD COST rule: `NHyp` untouched).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NHyp2

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

def P2HypC (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc lm : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnP2)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, lm]
      (fun s => (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y.toNat, yl.toNat)]
          (need xl.toNat yl.toNat lm.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl.toNat lm.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 0 < natVal s.mem y.toNat yl.toNat ∧ 1 ≤ lm.toNat ∧ lm.toNat ≤ 2 ^ 13 ∧
        0 < st.toNat ∧
        ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(z.toNat, z.toNat + 8 * zc.toNat)] ++ stWs s.mem st.toNat) ∧
          EvenHyp.StkApart s.mem st.toNat op 8) ∧ xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y.toNat yl.toNat % 2 ^ lm.toNat)
        (cost (stLen s.mem st.toNat) xl.toNat yl.toNat lm.toNat) s s')

/-- the old shape implies the new one (the new pre is stronger) -/
theorem P2HypC.of_P2Hyp {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need : Nat → Nat → Nat → Nat} {cost : Nat → Nat → Nat → Nat → Nat} (h : P2Hyp impl R ns stk above need cost) :
    P2HypC impl R ns stk above need cost :=
  fun b L z zl zc st x xl xc y yl yc lm => Ensures.mono (h b L z zl zc st x xl xc y yl yc lm) (fun _ h => h.1)
    (fun _ _ _ h => h)

end FvModexp.Arm64.NHyp2
