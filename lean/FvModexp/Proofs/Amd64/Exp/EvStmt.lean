import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the exported statement shape (asm s55; twin of infra's Arm64/Exp/EvStmt.lean)

`EvenSum impl R stk above need cost` = the `Summary` (`.full` form: no return-address-outside-program condition, so
the recursive pair `nat.expNN ↔ nat.expNNEven` composes; NESTED-PROGRAM RULE) of `nat.expNNEven` on `LibNE.program` at
its entry `fnE`. Arguments (amd64 ABIInternal, `EvDefs`): `z` RAX/RBX/RCX, `stk` RDI, `x` RSI/R8/R9 (`regs 0 3 1 7 6
8 9`); `y` at `RSP + 8 … + 24` and `m` at `RSP + 32 … + 48` (`NHyp.StkArg`, as `NHyp.SlowHyp`). The vocabulary is
amd64 `NHyp`'s (window `win s stk above`, which holds the return-address slot and the stack arguments):
* pre: the Summary entry facts (`X15 = 0`, `DF = 0`), the arguments, `NHyp.CPre … [x, y, m] (need xl yl ml)
  (cost ℓ xl yl ml)` (`ℓ` = the stack length at the entry) ∧ `0 < X` ∧ `2 ≤ Y` ∧ `0 < M` ∧ `M` even ∧ `xl ≤ 128` ∧
  `ml ≤ 128` ∧ `0 < st` ∧ `ml ≤ mc < 2^40` ∧ `z`'s range outside the window even when `cap z = 0` ∧ the package global
  `natOne` ∧ `zp, xc, yc < 2^64` ∧ the return address word below `2^47` (the `RetAddr` user-space bound) ∧
  `NHyp.XFacts` (as arm64) ∧ `ExpN.XG` (amd64 `nat.expNN`'s extra `x`/`natOne`/`hasADX` facts: `x` apart from the
  threshold globals, `natOne`'s word apart from them, `hasADX` readable, `x`'s full capacity readable and apart from
  the stack header and its free part; coordinator decision, asm s65) ∧ `x`'s capacity range outside the window;
* post: `RSP + 8`, `RBP`, `R14`, `X15` (the Summary exit) ∧ `NHyp.CPostR … (X ^ Y % M) (cost ℓ xl yl ml)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the entry facts (state `s`, arguments as naturals) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl yp yl mp ml mc : Nat) (s : State) : Prop :=
  NHyp.CPre R b L stk above zp zl zc st [(xp, xl), (yp, yl), (mp, ml)] (need xl yl ml)
      (cost (stLen s.mem st) xl yl ml) s ∧
    0 < natVal s.mem xp xl ∧ 2 ≤ natVal s.mem yp yl ∧ 0 < natVal s.mem mp ml ∧ natVal s.mem mp ml % 2 = 0 ∧
    xl ≤ 128 ∧ ml ≤ 128 ∧ 0 < st ∧ ml ≤ mc ∧ mc < 2 ^ 40 ∧ Outside zp (8 * zc) (win s stk above) ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      NHyp.StkApart s.mem st op 8

/-- the exit facts: the common callee exit shape with value `x^y mod m` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (cost : Nat → Nat → Nat → Nat → Nat) (zp zc st xp xl yp yl mp ml : Nat) (s s' : State) : Prop :=
  NHyp.CPostR R b L stk above zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml)
    (cost (stLen s.mem st) xl yl ml) s s'

/-- **the export shape** of `nat.expNNEven` (see the module doc) -/
def EvenSum (impl : List Amd64.Segment) (R : RtInv) (stk above : Nat) (need : Nat → Nat → Nat → Nat)
    (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp ml mc : Nat),
    Summary (LibNE.program.link impl) fnE
      (fun s => s.xmm 15 = 0 ∧ s.df = false ∧
        s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
        s.regs 7 = BitVec.ofNat 64 st ∧ s.regs 6 = BitVec.ofNat 64 xp ∧ s.regs 8 = BitVec.ofNat 64 xl ∧
        s.regs 9 = BitVec.ofNat 64 xc ∧ NHyp.StkArg s 0 yp yl yc ∧ NHyp.StkArg s 24 mp ml mc ∧
        Pre R b L stk above need cost zp zl zc st xp xl yp yl mp ml mc s ∧
        zp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧ yc < 2 ^ 64 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
        NHyp.XFacts R L xp xl xc ∧ ExpN.XG s.mem st xp xl xc ∧ Outside xp (8 * xc) (win s stk above))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ Post R b L stk above cost zp zc st xp xl yp yl mp ml s s')

end FvModexp.Amd64.ExpEven
