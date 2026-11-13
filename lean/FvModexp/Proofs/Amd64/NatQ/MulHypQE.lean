import FvModexp.Proofs.Amd64.NatQ.MulDefs

set_option autoImplicit false

/-!
# `nat.mul` (amd64) as `divRecursiveStep` uses it, Q-form: `Q.DivRec.MulHypQE` (owner of the statement: asm;
proof: divmc's amd64 Q `nat.mul` chain) — TIGHT COSTS

The amd64 twin of Arm64/NatQ/MulHypQE.lean. divmc's amd64 `Q.NatMul.MPost` already carries the exact-write clause
(`Exact`, = arm64's `ExactR`), so the statement is simply the `Ensures` of `nat.mul`'s member (`MPre` / `MPost` at the
window `W`) with the register arguments `z = (AX, BX, CX)`, `stk = DI`, `x = (SI, R8, R9)` and `y` passed on the stack
at `RSP + 8 / + 16 / + 24` (Go ABIInternal; bound by the pre's stack-slot conjuncts as `DivLarge.DrsPreW`'s `vpS…`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.DivRec

/-- **`nat.mul` as `divRecursiveStep` uses it, Q-form** (amd64; program `ns`, window `W`) -/
def MulHypQE (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (W : Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (yp yl yc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program Q.NatMul.fn)
      [z, zl, zc, st, x, xl, xc]
      (fun s => s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl ∧
        s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc ∧
        Q.NatMul.MPre R b H L W z.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat yp yl yc s)
      (fun s s' => Q.NatMul.MPost R b H L W z.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat yp yl yc s s')

end FvModexp.Amd64.Q.DivRec
