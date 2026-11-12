import FvModexp.Proofs.Amd64.Nat.DivBasicPro

set_option autoImplicit false

/-!
# `divBasic` (amd64): the relations between the segment lemmas (no proofs)

Collected here so that the segment modules import only this module and compile in parallel (ROW-TIME LESSON).
The twin of `Arm64/Nat/DivBasicRel.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

/-- the return address of `CALL (*stack).nat` (`callNat + 5`) -/
abbrev raNat : Nat := 6222484

/-- the facts right after `(*stack).nat` returned (state `S2`; `P` the call state) -/
structure AfterNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st vl : Nat) (s P S2 : State)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  pc : S2.rip = BitVec.ofNat 64 (callNat + 5)
  sp : S2.regs 4 = s.regs 4 - 224#64
  r5 : S2.regs 5 = s.regs 4 - 8#64
  r14 : S2.regs 14 = s.regs 14
  fs : S2.fsBase = s.fsBase
  x15 : S2.xmm 15 = 0#128
  df : S2.df = false
  r0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st + 8 * stLen s.mem st)
  r3 : S2.regs 3 = BitVec.ofNat 64 (vl + 1)
  r1 : S2.regs 1 = BitVec.ofNat 64 (vl + 1)
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) (vl + 1) ≤ b1
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S2.mem)
  ok : StkOK S2.mem R L1 st
  len : stLen S2.mem st = stLen s.mem st + (vl + 1 + 3) / 4 * 4
  same : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st →
    stW S2.mem st = stW s.mem st ∧ stCap S2.mem st = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 →
    InRanges (stW S2.mem st) (8 * stCap S2.mem st) R.rt ∧ ApartAll (stW S2.mem st) (8 * stCap S2.mem st) L
  F2 : MemFrame (P.mem.writeLE ((s.regs 4).toNat - 232) 8 raNat) S2.mem
    (R.rt ++ [((s.regs 4).toNat - 232 - 4192, (s.regs 4).toNat - 232 + 24)] ++ stkWs s.mem st)
  LF2 : LiveFrame (P.mem.writeLE ((s.regs 4).toNat - 232) 8 raNat) S2.mem L (stkWs s.mem st)
  mem : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 →
    (stW S2.mem st, stW S2.mem st + 8 * stCap S2.mem st) ∈ L1

/-- the state at the loop head with `Env` and `Mem` (`RDX = j` as a 64-bit word, `R8 = ujn`) -/
structure Hd (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (r2 ujn : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 head
  sp : S.regs 4 = s.regs 4 - 224#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  r0 : S.regs 0 = BitVec.ofNat 64 (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))
  r1 : S.regs 1 = BitVec.ofNat 64 vl
  r2 : S.regs 2 = BitVec.ofNat 64 r2
  r3 : S.regs 3 = BitVec.ofNat 64 (vl + 1)
  r6 : S.regs 6 = BitVec.ofNat 64 vp
  r7 : S.regs 7 = BitVec.ofNat 64 (vl + 1)
  r8 : S.regs 8 = BitVec.ofNat 64 ujn
  r10 : S.regs 10 = BitVec.ofNat 64 t
  r11 : S.regs 11 = BitVec.ofNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8)
  env : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem

/-- `qhatv[0:n] = mulAddVWW(…)` setup point (`CMPQ DI, CX`) -/
abbrev mulPt : Nat := segAddr Extracted.program fn + 0x26c

/-- the `CALL divWW` (return `+0x1ee`) -/
abbrev callWW : Nat := segAddr Extracted.program fn + 0x1e9

/-- the facts at `mulPt` (state `S'`), `S` the head state: the head's registers except `R8 = qhat` -/
structure AtMul (s S S' : State) (vp vl t rec vn1 j qhat : Nat) : Prop where
  pc : S'.rip = BitVec.ofNat 64 mulPt
  sp : S'.regs 4 = s.regs 4 - 224#64
  r5 : S'.regs 5 = s.regs 4 - 8#64
  r14 : S'.regs 14 = s.regs 14
  fs : S'.fsBase = s.fsBase
  x15 : S'.xmm 15 = 0#128
  df : S'.df = false
  r0 : S'.regs 0 = BitVec.ofNat 64 rec
  r1 : S'.regs 1 = BitVec.ofNat 64 vl
  r2 : S'.regs 2 = BitVec.ofNat 64 j
  r3 : S'.regs 3 = BitVec.ofNat 64 (vl + 1)
  r6 : S'.regs 6 = BitVec.ofNat 64 vp
  r7 : S'.regs 7 = BitVec.ofNat 64 (vl + 1)
  r8 : S'.regs 8 = BitVec.ofNat 64 qhat
  r10 : S'.regs 10 = BitVec.ofNat 64 t
  r11 : S'.regs 11 = BitVec.ofNat 64 vn1
  fr : MemFrame S.mem S'.mem [((s.regs 4).toNat - 232, (s.regs 4).toNat - 224), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)]
  jj : S'.mem.readLE ((s.regs 4).toNat - 96) 8 = j

/-- the frame facts at a point `pc` of the loop body after `R14`/`X15` were restored (`j` stored at `RSP-96`) -/
structure Bd (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (pc j : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 pc
  sp : S.regs 4 = s.regs 4 - 224#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  mem : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S.mem
  jj : S.mem.readLE ((s.regs 4).toNat - 96) 8 = j

/-- the `CALL mulAddVWW.abi0` (return `+0x2b2` = 6222994) and the point after `XORPS X15; MOVQ FS:-8, R14` -/
abbrev callVww : Nat := segAddr Extracted.program fn + 0x2ad
abbrev afterVww : Nat := segAddr Extracted.program fn + 0x2bf
/-- the `CALL subVV.abi0` (return 6223247) and after the restore -/
abbrev callSub : Nat := segAddr Extracted.program fn + 0x3aa
abbrev afterSub : Nat := segAddr Extracted.program fn + 0x3bc
/-- the `CALL addVV.abi0` (return 6223429) and after the restore -/
abbrev callAdd : Nat := segAddr Extracted.program fn + 0x460
abbrev afterAdd : Nat := segAddr Extracted.program fn + 0x472
/-- `ujn = u[j+n-1]`, the `q[j]` store and the back edge -/
abbrev tailPt : Nat := segAddr Extracted.program fn + 0x4c9

/-- a store into the stack window keeps the runtime's view -/
theorem view_win {R : RtInv} {lo n0 : Nat} (hout : Outside lo n0 R.rt) (L : List (Nat × Nat)) (m : Memory)
    (a n v : Nat) (h1 : lo ≤ a) (h2 : a + n ≤ lo + n0) : view R.rt L (m.writeLE a n v) = view R.rt L m :=
  view_writeLE_out (hout.of_sub h1 h2)

end FvModexp.Amd64.DivBasic
