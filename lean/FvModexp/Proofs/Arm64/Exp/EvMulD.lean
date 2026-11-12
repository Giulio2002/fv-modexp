import FvModexp.Proofs.Arm64.Nat.SqrMulX
import FvModexp.Proofs.Arm64.Exp.RdIn0

set_option autoImplicit false

/-!
# `nat.mul` (arm64) in the premise form `expNNEven` needs: `MulHypG` (agent infra)

`expNNEven` multiplies an operand that may be EMPTY with capacity `0` and a pointer that is `nil` or an empty runtime
slice (`z1 - z2 mod 2^n`, the truncated product): divmc's `EvenHyp.MulHypX0` asks `CapIn` (`Held x (8 xc)`) and
`(zp = x → zc = xc)` unguarded, which such an operand cannot give (an empty runtime slice may sit strictly inside a
runtime range; its pointer may coincide with an empty `z`'s). `MulHypG` = `MulHypX0` with
* `CapIn0`: the `Held` / bound part of `CapIn` under `0 < xc` (exactly divmc's internal `NatMul.Ops`),
* `MulXG`: `MulX` with the alias-capacity facts under `0 < zc → 0 < xl` (the internal `Ops` disjunction's
  right side is vacuous otherwise).
`MulPreG` is `EvenHyp.MulPre0` restated here (same body, `rfl`), so the segment modules need not import `nat.mul`'s
proof; `ExpEven.NatMulG.hypG` (module `EvMulG`) proves `MulHypG` from `NatMul.ens` (as divmc's `NatMul.hypX0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut)

/-- = divmc's `EvenHyp.MulPre0` (both operands `RdIn0`) -/
@[reducible] def MulPreG (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st x xl y yl : Nat)
    (s : State) : Prop :=
  CallEnv R L s stk above ∧ RunIface.Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧
    WrOut R L s stk above zp zc ∧
    RdIn0 R L s stk above x xl ∧ RdIn0 R L s stk above y yl ∧ xl ≤ 2 ^ 12 ∧ yl ≤ 2 ^ 12 ∧
    (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    (zp = y ∨ (0 < zc → 0 < yl → Apart zp (8 * zc) y (8 * yl))) ∧
    StkIn R L s stk above st ∧ stLen s.mem st + 4 * (xl + yl) + 64 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st x (8 * xl) ∧ StkApart s.mem st y (8 * yl) ∧
    c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- an operand's capacity facts, the array facts only for a non-empty capacity -/
@[reducible] def CapIn0 (R : RtInv) (L : List (Nat × Nat)) (x xl xc : Nat) : Prop :=
  xl ≤ xc ∧ xc < 2 ^ 40 ∧ (0 < xc → Held R L x (8 * xc) ∧ x + 8 * xc ≤ 2 ^ 48)

theorem CapIn.to0 {R : RtInv} {L : List (Nat × Nat)} {x xl xc : Nat} (h : CapIn R L x xl xc) : CapIn0 R L x xl xc :=
  ⟨h.1, h.2.1, fun _ => h.2.2⟩

/-- `MulX` with the alias-capacity facts guarded -/
@[reducible] def MulXG (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st zp zc x xl xc y yl yc : Nat) :
    Prop :=
  StkX R L s stk above st ∧ Outside zp (8 * zc) (win s stk above) ∧ (zp = x → 0 < zc → 0 < xl → zc = xc) ∧
    (zp = y → 0 < zc → 0 < yl → zc = yc) ∧ OpX s.mem st zp (8 * zc) ∧ OpX s.mem st x (8 * xl) ∧
    OpX s.mem st y (8 * yl)

/-- the premise form of `nat.mul` at `expNNEven`'s two products -/
def MulHypG (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPreG R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn0 R L x.toNat xl.toNat xc.toNat ∧
        CapIn0 R L y.toNat yl.toNat yc.toNat ∧
        MulXG R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat)
      (fun s s' => MulPostL R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat
        x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

end FvModexp.Arm64.ExpEven
