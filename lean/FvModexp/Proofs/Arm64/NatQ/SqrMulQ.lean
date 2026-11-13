import FvModexp.Proofs.Arm64.Nat.SqrMulX
import FvModexp.Proofs.Arm64.Nat.RtPostQ
import FvModexp.Proofs.Common.MulCostQ

set_option autoImplicit false

/-!
# Q-form export shapes of `nat.sqr` / `nat.mul` (arm64; owner divmc; TIGHT COSTS)

The twins of `EvenHyp.SqrHypX` / `MulHypX` (Nat/SqrMulX.lean) in the amortised-stack Q-form (Common/StackPot,
NOTES-conventions "[divmc s34] TIGHT COSTS step 2"): a reserve level `H` is ∀-quantified next to the budget,
* pre: infra's `SqrPre`/`MulPre` with the interface cost `c = C xl (yl) + stkR H s.mem st` (`C` level-free:
  `sqrCQ`/`mulCQ`), plus the level twin `stLen s.mem st + 4·(len) + 64 ≤ H` (the same `D` as the `2 ^ 16` bound);
* post: `SqrPostL`/`MulPostL` with `RtPostQ … c (stkR H s'.mem st) …` (`b - c + stkR H s'.mem st ≤ b'`) in place of
  `RtPost … c …` (`b - c ≤ b'`): the credit of a grown stack capacity comes back.
Sequential calls at the same `H` compose by adding the `C`s (`q_seq2`, Nat/RtPostQ.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.ExpHyp (NatOF stWs)

/-- `SqrPostL` in the Q-form (`r'` = the reserve left after the call, `stkR H s'.mem st`) -/
@[reducible] def SqrPostQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (2 * xl) p' l' c' (natVal s.mem x xl * natVal s.mem x xl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st → Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

/-- `MulPostL` in the Q-form -/
@[reducible] def MulPostQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl y yl : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (xl + yl) p' l' c' (natVal s.mem x xl * natVal s.mem y yl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st → Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

/-- **the Q-form `nat.sqr` premise** (`cost` level-free, e.g. `sqrCQ`) -/
def SqrHypQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPre R b (cost xl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat
        x.toNat xl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        SqrX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat ∧
        stLen s.mem st.toNat + 4 * (2 * xl.toNat) + 64 ≤ H)
      (fun s s' => SqrPostQ R b (cost xl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above z.toNat
        zc.toNat st.toNat x.toNat xl.toNat s s' ∧ Reuse (2 * xl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat)] s')

/-- **the Q-form `nat.mul` premise** (`cost` level-free, e.g. `mulCQ`) -/
def MulHypQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

end FvModexp.Arm64.EvenHyp
