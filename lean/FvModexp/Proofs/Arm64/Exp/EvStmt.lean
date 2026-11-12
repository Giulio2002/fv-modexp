import FvModexp.Proofs.Arm64.Exp.EvDefs
import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the exported statement shape (agent infra; accepted by expmc s28)

`EvenSum impl R stk above need cost` = the `Summary` (`.full` form: no return-address-outside-program condition, so
the recursive pair `nat.expNN ↔ nat.expNNEven` composes) of `nat.expNNEven` on `LibNE.program` (NESTED-PROGRAM RULE)
at its entry `fnE`, arguments `X0..X12 = [z, zl, zc, st, x, xl, xc, y, yl, yc, m, ml, mc]`:
* pre: `NHyp.CPre … [x, y, m] (need xl yl ml) (cost ℓ xl yl ml)` (`ℓ` = the stack length at the entry) ∧ `0 < X` ∧
  `2 ≤ Y` ∧ `0 < M` ∧ `M` even ∧ `xl ≤ 128` ∧ `ml ≤ 128` ∧ the package global `natOne` (as `NHyp.P2Hyp`) ∧ the
  return address `X30` 4-aligned below `2^48`;
* post: `sp`, `X18`, `X28`, `X29` kept ∧ `NHyp.CPostR … (X ^ Y % M) (cost ℓ xl yl ml)`.
infra proves `EvenSum` for explicit `stkE`/`needE`/`costE` (`ExpEven.full`); expmc consumes it at nat.expNN's even call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the entry facts (state `s`, arguments as naturals) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl yp yl mp ml : Nat) (s : State) : Prop :=
  NHyp.CPre R b L stk above zp zl zc st [(xp, xl), (yp, yl), (mp, ml)] (need xl yl ml)
      (cost (stLen s.mem st) xl yl ml) s ∧
    0 < natVal s.mem xp xl ∧ 2 ≤ natVal s.mem yp yl ∧ 0 < natVal s.mem mp ml ∧ natVal s.mem mp ml % 2 = 0 ∧
    xl ≤ 128 ∧ ml ≤ 128 ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      EvenHyp.StkApart s.mem st op 8

/-- the exit facts: ABI registers kept, the common callee exit shape with value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (cost : Nat → Nat → Nat → Nat → Nat) (zp zc st xp xl yp yl mp ml : Nat) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    NHyp.CPostR R b L stk above zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml)
      (cost (stLen s.mem st) xl yl ml) s s'

/-- **the export shape** of `nat.expNNEven` (see the module doc) -/
def EvenSum (impl : List Segment) (R : RtInv) (stk above : Nat) (need : Nat → Nat → Nat → Nat)
    (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp ml mc : Nat),
    Summary (LibNE.program.link impl) fnE
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
        s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
        s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 yp ∧ s.regs 8 = BitVec.ofNat 64 yl ∧
        s.regs 9 = BitVec.ofNat 64 yc ∧ s.regs 10 = BitVec.ofNat 64 mp ∧ s.regs 11 = BitVec.ofNat 64 ml ∧
        s.regs 12 = BitVec.ofNat 64 mc ∧
        Pre R b L stk above need cost zp zl zc st xp xl yp yl mp ml s ∧
        (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => Post R b L stk above cost zp zc st xp xl yp yl mp ml s s')

end FvModexp.Arm64.ExpEven
