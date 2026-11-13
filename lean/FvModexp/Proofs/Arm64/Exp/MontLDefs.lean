import FvModexp.Proofs.Arm64.Exp.MontHyp
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.montgomery` (arm64): the main loop's shared definitions (frame writes, post, loop invariant)

Split out of `MontLoop` (agent expmc s61) so that the loop body (`MontBody`) and the exit (`MontExit`) compile in
parallel; `MontLoop` composes them by induction.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.MontHyp

namespace FvModexp.Arm64.MontLoop

open FvModexp.Exp


/-- The loop head's frame-slot writes: the call frame `[sp+8, sp+104)` (and its result word), the spills
`[sp+128, sp+168)`, `[sp+176, sp+184)`. -/
abbrev loopWs (zp n sp : Nat) : List (Nat × Nat) :=
  [(zp, zp + 16 * n), (sp + 8, sp + 104), (sp + 128, sp + 168), (sp + 176, sp + 184)]

/-- What the loop (with the exit path) guarantees, relative to the memory `M0` at the first arrival at the head. -/
abbrev LoopPost (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (s : State) (sp zp cap n X Y Mv k : Nat) (M0 : Memory)
    (s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
  s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 1 = BitVec.ofNat 64 n ∧ s'.regs 2 = BitVec.ofNat 64 cap ∧
  s'.mem.readLE zp (8 * n) = montgomery n X Y Mv k ∧
  R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
  MemFrame M0 s'.mem (R.rt ++ [(sp - 4096, sp + 184), (sp + 200, sp + 312), (zp, zp + 16 * n)]) ∧
  LiveFrame M0 s'.mem L [(zp, zp + 16 * n)]


/-- the loop statement after `r` remaining iterations (`MontLoop.loop` is `∀ r, Inv … r`) -/
def Inv (impl : List Segment) (R : RtInv) (ret : Nat) (s : State) (L : List (Nat × Nat)) (b : Nat)
    (sp zp cap xp xc yp mp mc k n : Nat) (M0 : Memory) (r : Nat) : Prop :=
  ∀ (S : State) (i c : Nat) (M : Memory), i + r = n →
    S.pc = BitVec.ofNat 64 head → S.sp = BitVec.ofNat 64 sp →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 (2 * n) → S.regs 2 = BitVec.ofNat 64 cap →
    S.regs 3 = BitVec.ofNat 64 xp → S.regs 4 = BitVec.ofNat 64 n → S.regs 5 = BitVec.ofNat 64 xc →
    S.regs 6 = BitVec.ofNat 64 yp → S.regs 7 = BitVec.ofNat 64 i → S.regs 8 = BitVec.ofNat 64 c →
    S.regs 9 = BitVec.ofNat 64 mp → S.regs 10 = BitVec.ofNat 64 n → S.regs 11 = BitVec.ofNat 64 mc →
    S.regs 12 = BitVec.ofNat 64 k → S.regs 13 = BitVec.ofNat 64 n →
    S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 → S.mem = M →
    MemFrame M0 M (loopWs zp n sp) →
    M.readLE zp (8 * (2 * n)) = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).1 →
    c = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).2 →
    Reaches ((LibMont.program.link impl).withExit ret) S (IsReturn fun s' =>
      LoopPost R L b s sp zp cap n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k M0 s')

end FvModexp.Arm64.MontLoop
