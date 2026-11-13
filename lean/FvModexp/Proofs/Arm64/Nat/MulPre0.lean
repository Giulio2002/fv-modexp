import FvModexp.Proofs.Arm64.Exp.MulHyp
import FvModexp.Proofs.Arm64.Exp.RdIn0
import FvModexp.Proofs.Arm64.Nat.NatAddDefs

set_option autoImplicit false

/-!
# Light home of `EvenHyp.MulPre0` / `MulPre.to0` / `ExactE` and `NatMul.wordT_rt'` (owner divmc)

Moved verbatim out of `Nat/MulHypX.lean` (which imports this module) so that `NatQ/MulHypQ.lean` no longer imports
`Nat/MulHypX` and with it the whole OLD `nat.mul` chain (row-time trim, divmc s48).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut RtPost NatOF stWs)

/-- infra's `MulPre` with both operands empty-tolerant (`RdIn0`) -/
@[reducible] def MulPre0 (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st x xl y yl : Nat)
    (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧
    WrOut R L s stk above zp zc ∧
    RdIn0 R L s stk above x xl ∧ RdIn0 R L s stk above y yl ∧ xl ≤ 2 ^ 12 ∧ yl ≤ 2 ^ 12 ∧
    (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    (zp = y ∨ (0 < zc → 0 < yl → Apart zp (8 * zc) y (8 * yl))) ∧
    StkIn R L s stk above st ∧ stLen s.mem st + 4 * (xl + yl) + 64 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st x (8 * xl) ∧ StkApart s.mem st y (8 * yl) ∧
    c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem MulPre.to0 {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st x xl y yl : Nat} {s : State}
    (h : MulPre R b c L stk above zp zl zc st x xl y yl s) : MulPre0 R b c L stk above zp zl zc st x xl y yl s := by
  obtain ⟨h1, h2, h3, h4, h5, hx, hy, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, hx.toRdIn0, hy.toRdIn0, h6⟩

/-- the exact-write clause on the result registers (= asm's `DivRec.ExactR`, same body) -/
@[reducible] def ExactE (R : RtInv) (L : List (Nat × Nat)) (ws : List (Nat × Nat))
    (need zp zc st xp xc yp yc v : Nat) (s s' : State) : Prop :=
  need ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc →
    s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 2 = BitVec.ofNat 64 zc ∧
    (natVal s'.mem zp need = v ∨ (v = 0 ∧ natVal s'.mem zp need = natVal s.mem zp need)) ∧
    MemFrame s.mem s'.mem (R.rt ++ ws ++ [(zp, zp + 8 * need)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(zp, zp + 8 * need)] ++ stkWs s.mem st)

end FvModexp.Arm64.EvenHyp

namespace FvModexp.Arm64.NatMul

set_option maxRecDepth 20000 in
theorem wordT_rt' {R : RtInv} (hro : RoOut R) : Outside NatAdd.wordT 16 R.rt :=
  RoOut.out' hro 1 (by decide) (by decide)

end FvModexp.Arm64.NatMul
