import FvModexp.Proofs.Arm64.NatQ.SqrMulQ

set_option autoImplicit false

/-!
# `nat.mul` (arm64) in the Q-form WITH the exact-write clause: `Q.DivRec.MulHypQE` (owner of the statement: asm;
proof: divmc's Q `nat.mul` chain) — TIGHT COSTS

`divRecursiveStep` calls `qhatv.mul(stk, qhat, v[:s])` and later reads `qhatv[:s]` beyond the product's length (the
zeros left by `clear(qhatv)`), so it needs the exact-write clause of the old `DivRec.MulHypXE` (`ExactR`, body = divmc's
`EvenHyp.ExactE`). `MulHypQE` = divmc's `EvenHyp.MulHypQ` with `ExactR` in place of `Reuse` in the post (the pre is
`MulHypQ`'s verbatim). A separate small module so that the `nat.mul` chain need not import asm's.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.DivRec

/-- the exact-write clause on the result registers (body = `FvModexp.Arm64.DivRec.ExactR` = `EvenHyp.ExactE`) -/
@[reducible] def ExactR (R : RtInv) (L : List (Nat × Nat)) (ws : List (Nat × Nat))
    (need zp zc st xp xc yp yc v : Nat) (s s' : State) : Prop :=
  need ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc →
    s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 2 = BitVec.ofNat 64 zc ∧
    (natVal s'.mem zp need = v ∨ (v = 0 ∧ natVal s'.mem zp need = natVal s.mem zp need)) ∧
    MemFrame s.mem s'.mem (R.rt ++ ws ++ [(zp, zp + 8 * need)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(zp, zp + 8 * need)] ++ stkWs s.mem st)

/-- **`nat.mul` as `divRecursiveStep` uses it, Q-form** (`cost` level-free, e.g. `mulCQ`) -/
def MulHypQE (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program EvenHyp.fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => EvenHyp.MulPre R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat
        zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ EvenHyp.CapIn R L x.toNat xl.toNat xc.toNat ∧
        EvenHyp.CapIn R L y.toNat yl.toNat yc.toNat ∧
        EvenHyp.MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => EvenHyp.MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L
        stk above z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        ExactR R L (winA s stk above) (xl.toNat + yl.toNat) z.toNat zc.toNat st.toNat x.toNat xc.toNat y.toNat yc.toNat
          (natVal s.mem x.toNat xl.toNat * natVal s.mem y.toNat yl.toNat) s s')

end FvModexp.Arm64.Q.DivRec
