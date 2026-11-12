import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the exported statement shape (agent expmc)

* `ExpSlow.cost sqC mlC dvC ℓ xl yl ml`: `z.set(x)`'s `makeslice` plus `64 · yl` loop bodies (at most `w ≤ 63` top
  iterations and `64 (yl - 1)` lower ones), each bounded by the box maxima of the callee costs over the lengths the
  loop can see (`len z ≤ 128` at `sqr`, `≤ 256` at `mul`, `≤ 384` at `div`; `stk`'s length is constant `ℓ`).
* `SlowHypA` = `NHyp.SlowHyp` with ONE more pre conjunct `SlowX R L x xl xc` (FINDING part 2 of NOTES-conventions
  "[expmc s37]"): `zz.mul(stk, z, x)` multiplies by the INPUT `x`, and every `nat.mul` premise form needs of its
  operands the capacity facts (`CapIn0`: `xl ≤ xc < 2^40`, the cap range held — Go's `alias` compares cap ends;
  cf. infra's `P2HypC`) and apartness from the threshold globals `gA` (`OpX`). The coordinator decides where they
  come from (`RunIface.ExpSpec`'s `x.abs` has both). Post `CPostR0` = `CPostR` with `NatOF0`: a `nil` result allowed
  (FINDING part 3; `ExpN.Post` already has that disjunct).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- the budget bound of `nat.expNNSlow` (see the module doc) -/
def cost (sqC : Nat → Nat → Nat) (mlC dvC : Nat → Nat → Nat → Nat) (ℓ xl yl ml : Nat) : Nat :=
  makeCost xl + 64 * yl * (Exp.supN (sqC ℓ) 128 + Exp.supN (fun n => mlC ℓ n xl) 256 + Exp.supN (fun n => dvC ℓ n ml) 384)

/-- `ExpHyp.NatOF` with need `1` and the EMPTY result allowed `nil` (`(0, 0, 0)`: the last `div`'s remainder in a
`nil` `r` buffer, e.g. `modexp(2, 4, 4)`; FINDING part 3 of NOTES-conventions "[expmc s37]"); the three location
disjuncts are `ExpN.Post`'s -/
@[reducible] def NatOF0 (R : RtInv) (L L' : List (Nat × Nat)) (m' : Memory) (zp zc p' l' c' v : Nat) : Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    ((c' = 0 ∧ p' = 0) ∨ (p' = zp ∧ c' = zc) ∨ (1 ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))

/-- `NHyp.CPostR` with `NatOF0` -/
@[reducible] def CPostR0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF0 R L L' s'.mem zp zc p l c v ∧ ExpHyp.RtPost R b cst L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the extra facts of the operand `x` (see the module doc) -/
@[reducible] def SlowX (R : RtInv) (L : List (Nat × Nat)) (x xl xc : Nat) : Prop :=
  (xl ≤ xc ∧ xc < 2 ^ 40 ∧ (0 < xc → Held R L x (8 * xc) ∧ x + 8 * xc ≤ 2 ^ 48)) ∧
    (0 < xl → Apart x (8 * xl) RunIface.gA 32)

/-- `NHyp.SlowHyp` + `SlowX`, post `CPostR0` (see the module doc) -/
def SlowHypA (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program NHyp.fnSlow)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]
      (fun s => (NHyp.CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat
          [(x.toNat, xl.toNat), (y.toNat, yl.toNat), (m.toNat, ml.toNat)]
          (need xl.toNat yl.toNat ml.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl.toNat ml.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 2 ≤ natVal s.mem y.toNat yl.toNat ∧ 0 < natVal s.mem m.toNat ml.toNat ∧
        0 < st.toNat) ∧ SlowX R L x.toNat xl.toNat xc.toNat)
      (fun s s' => CPostR0 R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y.toNat yl.toNat % natVal s.mem m.toNat ml.toNat)
        (cost (stLen s.mem st.toNat) xl.toNat yl.toNat ml.toNat) s s')

end FvModexp.Arm64.ExpSlow
