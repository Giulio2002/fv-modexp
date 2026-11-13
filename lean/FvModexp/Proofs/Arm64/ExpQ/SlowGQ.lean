import FvModexp.Proofs.Arm64.NatQ.SqrMulQ
import FvModexp.Proofs.Arm64.ExpQ.SlowQStmt

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64), Q-form: the empty-tolerant callee premise forms of its `sqr` / `mul` calls (agent expmc s43)

The Q twins (Common/StackPot; divmc's `EvenHyp.SqrHypQ`/`MulHypQ` shape) of `ExpSlow.SqrHypG` (SlowG.lean) and
infra's `ExpEven.MulHypG` (EvMulD.lean): the reserve level `H` ∀-quantified before `b`, the pre's cost `cost … +
stkR H s.mem st` and the LAST conjunct the level twin (`stLen + 4·(2·len x) + 64 ≤ H` / `stLen + 4·(len x + len y) + 64
≤ H`), the posts `SqrPostQ`/`MulPostQ`. `div` is asm's `ExpSlow.DivHypLGQ` (NatQ/DivHypQ.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.EvenHyp FvModexp.Arm64.ExpSlow
open FvModexp.Arm64.ExpEven (CapIn0 MulPreG MulXG)

/-- **`nat.sqr`**, empty-tolerant operand, Q-form (`cost` level-free, e.g. `sqrCQ`) -/
def SqrHypGQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPreG R b (cost xl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat
        x.toNat xl.toNat s ∧ CapIn0 R L x.toNat xl.toNat xc.toNat ∧
        SqrXG R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat ∧
        stLen s.mem st.toNat + 4 * (2 * xl.toNat) + 64 ≤ H)
      (fun s s' => SqrPostQ R b (cost xl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above z.toNat
        zc.toNat st.toNat x.toNat xl.toNat s s' ∧ (xl.toNat = 0 → s'.regs 0 = z ∧ s'.regs 2 = zc))

/-- **`nat.mul`**, empty-tolerant operands, Q-form (`cost` level-free, e.g. `mulCQ`) -/
def MulHypGQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPreG R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn0 R L x.toNat xl.toNat xc.toNat ∧
        CapIn0 R L y.toNat yl.toNat yc.toNat ∧
        MulXG R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

end FvModexp.Arm64.Q.ExpSlow
