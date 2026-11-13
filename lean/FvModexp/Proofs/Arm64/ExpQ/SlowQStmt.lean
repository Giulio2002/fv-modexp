import FvModexp.Proofs.Arm64.NatQ.DivHypQ
import FvModexp.Proofs.Arm64.Exp.SlowStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64), Q-form (TIGHT COSTS) export statement (agent expmc s43)

The amortised-stack twin (Common/StackPot, NOTES-conventions "[divmc s34]/[divmc s35] TIGHT COSTS") of
`NHyp.SlowHyp`: `expNNSlow`'s loop makes `64 · len y` rounds of `sqr`/`mul`/`div` on the SAME stack, so the reserve
`stkR H` must be paid once (a per-call reserve is ~10^6 bytes per round at 128 words).
* `Q.ExpSlow.costQ sqC mlC dvC xl yl ml` — level-free: `z.set(x)`'s `makeslice` + `64 · yl` rounds, each bounded by
  the box maxima of the level-free callee costs (`sqrCQ`, `mulCQ`, `Q.NatDiv.costQ Q.drsCQ`) over the lengths the loop
  sees (`len z ≤ M` at `sqr`, `≤ 2M` at `mul`, `≤ 3M` at `div`, `M = max (len x) (len m)`), as `ExpSlow.cost`.
* `Q.ExpSlow.needH xl ml = 48 · max xl ml + 64` — the level twin: every callee's level bound (`sqr` `4·(2·len z) + 64`,
  `mul` `4·(len z + len x) + 64`, `div` `16·len u + 64`) at the constant stack length of the loop is `≤ stLen + needH`.
* `NHyp.SlowHypQ … need needH cost`: `SlowHyp`'s pre with the interface cost `cost xl yl ml + stkR H s.mem st` and
  the LAST conjunct `stLen s.mem st + needH xl ml ≤ H`; post `CPostR0Q` (= `CPostR0` with `RtPostQ`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

/-- the level-free budget of `nat.expNNSlow` (see the module doc) -/
def costQ (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl yl ml : Nat) : Nat :=
  makeCost xl + 64 * yl * (Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC n ml) (3 * max xl ml))

/-- the level twin of `nat.expNNSlow` (see the module doc) -/
@[reducible] def needH (xl ml : Nat) : Nat := 48 * max xl ml + 64

end FvModexp.Arm64.Q.ExpSlow

namespace FvModexp.Arm64.NHyp

open FvModexp.Arm64.ExpHyp

/-- `CPostR0` in the Q-form (`c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def CPostR0Q (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v c r' : Nat)
    (s s' : State) : Prop :=
  ∃ p l cp : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 cp ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF0 R L L' s'.mem zp zc p l cp v ∧ RtPostQ R b c r' L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p cp

/-- **`nat.expNNSlow`, Q-form** (twin of `SlowHyp`; `cost` level-free, e.g. `Q.ExpSlow.costQ sqrCQ mulCQ
(Q.NatDiv.costQ Q.drsCQ)`; `needH` the level twin, the LAST pre conjunct) -/
def SlowHypQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (needH : Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc m ml mc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSlow)
      [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]
      (fun s => (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat
          [(x.toNat, xl.toNat), (y.toNat, yl.toNat), (m.toNat, ml.toNat)]
          (need xl.toNat yl.toNat ml.toNat) (cost xl.toNat yl.toNat ml.toNat + stkR H s.mem st.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 2 ≤ natVal s.mem y.toNat yl.toNat ∧ 0 < natVal s.mem m.toNat ml.toNat ∧
        0 < st.toNat) ∧ XFacts R L x.toNat xl.toNat xc.toNat ∧ stLen s.mem st.toNat + needH xl.toNat ml.toNat ≤ H)
      (fun s s' => CPostR0Q R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y.toNat yl.toNat % natVal s.mem m.toNat ml.toNat)
        (cost xl.toNat yl.toNat ml.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s')

end FvModexp.Arm64.NHyp
