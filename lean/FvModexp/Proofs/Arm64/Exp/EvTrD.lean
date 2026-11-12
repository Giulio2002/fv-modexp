import FvModexp.Proofs.Arm64.Exp.EvJ12
import FvModexp.Proofs.Arm64.Exp.RdIn0
import FvModexp.Proofs.Arm64.Nat.NatAdd0Defs

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the `trunc` / `add` premise forms (agent infra)

* `TrHyp0` = asm's `Trunc.Hyp0` (Nat/TruncE0.lean) restated with the same body (`TrPre0` = `Trunc.TruncPre0`), so the
  segment modules need not import `nat.trunc`'s proof; `Trunc.ens0` is an instance by `rfl`.
* `AddHypR0` = infra's `SubMod2N.AddHypR` with divmc's empty-tolerant `NatAdd.Pre0` (`NatAdd.ensR0` is an instance).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.RunIface (Serves)

/-- = `Trunc.TruncPre0` -/
@[reducible] def TrPre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl n : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ ExpHyp.WrOut R L s stk above zp zc ∧
    ExpHyp.RdIn0 R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (EvenHyp.truncNeed xl n) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- = `Trunc.Hyp0` -/
def TrHyp0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program Trunc.fn)
      [z, zl, zc, x, xl, xc, n]
      (fun s => TrPre0 R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s ∧
        (NatNorm s.mem x.toNat xl.toNat ∨ (n.toNat + 63) / 64 ≤ xl.toNat) ∧
        (z.toNat = x.toNat ∨ 0 < zc.toNat ∨ (0 < xl.toNat ∧ 0 < n.toNat)) ∧ (xl.toNat = 0 → z.toNat = x.toNat))
      (fun s s' => EvenHyp.TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

/-- `SubMod2N.AddHypR` with `NatAdd.Pre0` (empty-tolerant operands) -/
def AddHypR0 (impl : List Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatAdd.names).link impl) (segAddr Extracted.program NatAdd.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatAdd.Pre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatAdd.Post R b L zp zc xp xl yp yl s s' ∧
        (NatAdd.need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (NatAdd.mx xl yl < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40))

end FvModexp.Arm64.ExpEven
