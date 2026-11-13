import FvModexp.Proofs.Arm64.NatQ.DivBasicPro
import FvModexp.Proofs.Arm64.NatQ.DivBasicMemF
import FvModexp.Proofs.Common.AsmDivVW

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivBasicRel.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the relations between the segment lemmas (no proofs)

Collected here so that the segment modules (pro2, pro3, est, mul, sub, add, tail) import only this module and
compile in parallel (Janus compiles independent modules at once).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic
variable {H : Nat}

/-- the facts right after `(*stack).nat` returned (state `S2`; `P` the call state) -/
structure AfterNat (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (st vl : Nat) (s P S2 : State) (stkSN abSN : Nat)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  pc : S2.pc = BitVec.ofNat 64 (callNat + 4)
  sp : S2.sp = s.sp - 240#64
  r28 : S2.regs 28 = s.regs 28
  r29 : S2.regs 29 = s.sp - 248#64
  r18 : S2.regs 18 = s.regs 18
  r0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st + 8 * stLen s.mem st)
  r1 : S2.regs 1 = BitVec.ofNat 64 (vl + 1)
  r2 : S2.regs 2 = BitVec.ofNat 64 (vl + 1)
  ext : LiveExt R L L1
  bud : b - stkR H s.mem st + stkR H S2.mem st ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S2.mem)
  ok : StkOK S2.mem R L1 st
  len : stLen S2.mem st = stLen s.mem st + (vl + 1 + 3) / 4 * 4
  same : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st →
    stW S2.mem st = stW s.mem st ∧ stCap S2.mem st = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 →
    InRanges (stW S2.mem st) (8 * stCap S2.mem st) R.rt ∧ ApartAll (stW S2.mem st) (8 * stCap S2.mem st) L
  F2 : MemFrame P.mem S2.mem (R.rt ++ [(s.sp.toNat - 240 - stkSN, s.sp.toNat - 248),
    (s.sp.toNat - 232, s.sp.toNat - 240 + abSN)] ++ stkWs s.mem st)
  LF2 : LiveFrame P.mem S2.mem L (stkWs s.mem st)
  mem : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 →
    (stW S2.mem st, stW S2.mem st + 8 * stCap S2.mem st) ∈ L1

/-- the `CALL reciprocalWord` -/
abbrev callRec : Nat := segAddr Extracted.program fn + 0xac

/-- the state at the loop head (`R1 = r1` = `j` as a 64-bit word, `R2 = ujn`, `R0 = rec`) with `Env` and `Mem` -/
structure Hd (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (r1 ujn : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 head
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))
  r1 : S.regs 1 = BitVec.ofNat 64 r1
  r2 : S.regs 2 = BitVec.ofNat 64 ujn
  env : Env R b H L qp ql st up ul uc vp vl s t L1 b1 w1 c1
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem

/-- `qhatv[0:n] = mulAddVWW(…)` setup point -/
abbrev mulPt : Nat := segAddr Extracted.program fn + 0x160

/-- the facts at `mulPt` (state `S'`), `S` the head state -/
structure AtMul (s S S' : State) (j qhat : Nat) : Prop where
  pc : S'.pc = BitVec.ofNat 64 mulPt
  sp : S'.sp = s.sp - 240#64
  r28 : S'.regs 28 = s.regs 28
  r29 : S'.regs 29 = s.sp - 248#64
  r18 : S'.regs 18 = s.regs 18
  r2 : S'.regs 2 = BitVec.ofNat 64 qhat
  fr : MemFrame S.mem S'.mem [(s.sp.toNat - 80, s.sp.toNat - 72), (s.sp.toNat - 64, s.sp.toNat - 56)]
  jj : S'.mem.readLE (s.sp.toNat - 80) 8 = j

abbrev callWW : Nat := segAddr Extracted.program fn + 0x110

/-- the frame facts at a point `pc` of the loop body (`j` stored at `SP-80`) -/
structure Bd (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (pc j : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 pc
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem
  jj : S.mem.readLE (s.sp.toNat - 80) 8 = j

/-- a store into the stack window keeps the runtime's view -/
theorem view_win {R : RtInv} {lo n0 : Nat} (hout : Outside lo n0 R.rt) (L : List (Nat × Nat)) (m : Memory)
    (a n v : Nat) (h1 : lo ≤ a) (h2 : a + n ≤ lo + n0) : view R.rt L (m.writeLE a n v) = view R.rt L m :=
  view_writeLE_out (hout.of_sub h1 h2)

abbrev callVww : Nat := segAddr Extracted.program fn + 0x190

abbrev afterVww : Nat := segAddr Extracted.program fn + 0x194

abbrev afterSub : Nat := segAddr Extracted.program fn + 0x230

/-- `qhl` (natdiv.go:705-708) -/
@[reducible] def qhlOf (j vl ul c : Nat) : Nat := if ul < j + (vl + 1) ∧ c = 0 then vl else vl + 1

abbrev tailPt : Nat := segAddr Extracted.program fn + 0x2d8

/-- what the continuation of the add-back gets (`S` at `+0x230`, `S'` at `+0x2d8`) -/
@[reducible] def AddK (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S S' : State) (j qhat q bw : Nat) : Prop :=
  Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' tailPt j ∧ S'.regs 0 = BitVec.ofNat 64 vl ∧
    S'.regs 4 = BitVec.ofNat 64 ul ∧ S'.regs 7 = BitVec.ofNat 64 up ∧
    S'.regs 2 = BitVec.ofNat 64 (if bw = 0 then qhat else (qhat + 2 ^ 64 - 1) % 2 ^ 64) ∧
    MemFrame S.mem S'.mem (scr s ++ [(up + 8 * j, up + 8 * j + 8 * q)]) ∧
    (bw = 0 → ∀ a n, S'.mem.readLE a n = S.mem.readLE a n) ∧
    (bw ≠ 0 → ∃ ca, natVal S'.mem (up + 8 * j) vl + 2 ^ (64 * vl) * ca = natVal S.mem (up + 8 * j) vl + natVal s.mem vp vl ∧
      (vl < q → S'.mem.readLE (up + 8 * j + 8 * vl) 8 = (S.mem.readLE (up + 8 * j + 8 * vl) 8 + ca) % 2 ^ 64))

/-- the `continue` of natdiv.go:719 -/
@[reducible] def skipQ (j ul vl ql qh : Nat) : Prop := j = ul - vl ∧ ul - vl = ql ∧ qh = 0

end FvModexp.Arm64.Q.DivBasic
