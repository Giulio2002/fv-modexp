import FvModexp.Proofs.Amd64.Nat.LibDivL
import FvModexp.Proofs.Amd64.Nat.LibDrs
import FvModexp.Proofs.Amd64.Nat.DivBasic
import FvModexp.Proofs.Amd64.Exp.ExpHyp

set_option autoImplicit false

/-!
# `(z nat) divLarge(stk *stack, u, uIn, vIn nat) (q, r nat)` (go-bigmodexpfix natdiv.go:597), amd64 — statements

The amd64 twin of `Arm64/Nat/DivLargeDefs.lean` (same Go source, same model). Go ABIInternal: `RAX, RBX, RCX = z`,
`RDI = stk`, `RSI, R8, R9 = u` (the remainder's storage); `uIn` and `vIn` do not fit in the nine integer argument
registers and are passed ON THE STACK at `RSP + 8, + 16, + 24` and `RSP + 32, + 40, + 48` (13 words); results
`RAX, RBX, RCX = q`, `RDI, RSI, R8 = r`. Frame: `PUSHQ BP; SUBQ $0x128, SP` (`SP' = RSP - 304`); spills `z.ptr`
`RSP + 56`, `z.cap` `+ 72`, `stk` `+ 80`, `u.ptr` `+ 88`, `u.cap` `+ 104` (`above = 112`). The window `41272 =
312 + 40960` covers the deepest callee `divRecursiveStep` (entry `RSP - 312`, window `40960 / 96`, see `DrsPre`).
Locals (offsets from the ENTRY `RSP`): saved `RBP` `-8`, defer record `{deferwrap1, stk, len(stk.w)}` at `-40, -32,
-24`, its address at `-16`; result `q` `-64 … -48`, `r` `-88 … -72`; `v = stk.nat(n)` `-96` (ptr), `-160` (len),
`-152` (cap); `u` (after `u.make`) ptr `-104`, len `-200`, cap `-184`; `m = len uIn - n` `-128`; `len uIn + 1`
`-136`; `vIn[n-1]` `-168`; `shift` `-176`; the defer bit (byte) `-209`.

`divRecursiveStep` (natdiv.go:750) is a premise here (`DrsHyp`); `divLarge`'s statement is the internal summary that
`nat.div` / `nat.rem` compose.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.DivLarge

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge"
def drsFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep"
def names : List String := LibDivL.names
/-- the program of `divRecursiveStep`'s statement: the division tree without `divLarge` (and `nat.div`) -/
def drsNames : List String := LibDrs.names

/-- the `*stack` object of a callee with window `win s stk above` (amd64 twin of `Arm64.EvenHyp.StkIn`) -/
@[reducible] def StkIn (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st : Nat) : Prop :=
  StkOK s.mem R L st ∧ Outside st 24 (win s stk above) ∧ Apart st 24 ((s.regs 14).toNat + 16) 8 ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8)

/-! ## `divRecursiveStep` (natdiv.go:750) — the callee's statement

Args `RAX, RBX, RCX = z (q)`, `RDI = stk`, `RSI, R8, R9 = u`, `R10 = depth`, `v` on the stack (`RSP + 8 … + 24`).
Value contract as arm64 (`Mdl.RecOk`): `z` all zero, `v` with its top bit set, `2·U < 2^(64·(len v + len z))` →
`z = U / V`, `u = U mod V` in place. Window `40960 / 96` (frame 400 per level as arm64). -/

/-- The precondition of `divRecursiveStep` with the stack window `W` (register args `z = (qp, ql, qc)`, `st`, `u = (up, ul, uc)`, `depth` in `R10`; the stack args `v = (vp, vl, vc)` at `RSP + 8, + 16, + 24`); a plain conjunction (conjuncts in order: ce, sv, gl, qlc, qc40, ulc, uc40, vlc, vc40, v2, v9, vtop, q0, room, qa, ua, va, qu, qv, uv, sti, stl, sq, su, sv2, wbap, hf, fw, ga, cost, inv, vpS, vlS, vcS, tl; accessors `DrsPreW.<name>`). -/
def DrsPreW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost W : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  (CallEnv R L s W 96) ∧
  (Serves R) ∧
  (RunIface.Globals R s.mem (win s W 96)) ∧
  (ql ≤ qc) ∧
  (qc < 2 ^ 40) ∧
  (ul ≤ uc) ∧
  (uc < 2 ^ 40) ∧
  (vl ≤ vc) ∧
  (vc < 2 ^ 40) ∧
  (2 ≤ vl) ∧
  (vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9) ∧
  (2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) ∧
  (natVal s.mem qp ql = 0) ∧
  (2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql))) ∧
  (s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧ Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧ Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 14).toNat + 16) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧ Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48) ∧
  (Apart qp (8 * ql) up (8 * ul)) ∧
  (Apart qp (8 * ql) vp (8 * vl)) ∧
  (Apart up (8 * ul) vp (8 * vl)) ∧
  (StkIn R L s W 96 st) ∧
  (stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧ Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧ (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0)) ∧
  (Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96)) ∧
  (Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  (cost ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl) ∧
  (s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc) ∧
  (Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 ∧ Apart up (8 * ul) (s.fsBase.toNat - 8) 8 ∧ Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8)

theorem DrsPreW.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : CallEnv R L s W 96 := h.1
theorem DrsPreW.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Serves R := h.2.1
theorem DrsPreW.gl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : RunIface.Globals R s.mem (win s W 96) := h.2.2.1
theorem DrsPreW.qlc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : ql ≤ qc := h.2.2.2.1
theorem DrsPreW.qc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : qc < 2 ^ 40 := h.2.2.2.2.1
theorem DrsPreW.ulc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : ul ≤ uc := h.2.2.2.2.2.1
theorem DrsPreW.uc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : uc < 2 ^ 40 := h.2.2.2.2.2.2.1
theorem DrsPreW.vlc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : vl ≤ vc := h.2.2.2.2.2.2.2.1
theorem DrsPreW.vc40 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : vc < 2 ^ 40 := h.2.2.2.2.2.2.2.2.1
theorem DrsPreW.v2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : 2 ≤ vl := h.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.v9 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : vl ≤ 2 ^ 9 ∧ ql ≤ 2 ^ 9 := h.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vtop {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.q0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : natVal s.mem qp ql = 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.room {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : 2 * natVal s.mem up ul < 2 ^ (64 * (vl + ql)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qa {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible qp (8 * ql) true = true ∧ qp + 8 * ql ≤ 2 ^ 48 ∧ Held R L qp (8 * ql) ∧ Outside qp (8 * ql) (win s W 96) ∧ Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.ua {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible up (8 * ul) true = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧ Outside up (8 * ul) (win s W 96) ∧ Apart up (8 * ul) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.va {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.accessible vp (8 * vl) false = true ∧ vp + 8 * vl ≤ 2 ^ 48 ∧ Held R L vp (8 * vl) ∧ Outside vp (8 * vl) (win s W 96) ∧ Apart vp (8 * vl) RunIface.gA 32 ∧ Held R L vp (8 * vc) ∧ vp + 8 * vc ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.qv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.uv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart up (8 * ul) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sti {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : StkIn R L s W 96 st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.stl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : stLen s.mem st + 12 * vl + 64 ≤ 2 ^ 16 ∧ 0 < stCap s.mem st ∧ Apart vp (8 * vc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧ (st ≠ 0 ∧ up % 8 = 0 ∧ qp % 8 = 0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sq {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) st 24 ∧ Apart qp (8 * ql) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.su {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.sv2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.wbap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.hf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.fw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s W 96) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.ga {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) RunIface.gA 32 ∧ Apart up (8 * ul) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : cost ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vpS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vlS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.vcS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem DrsPreW.tl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {cost W : Nat} {qp ql qc st up ul uc vp vl vc : Nat} {s : State}
    (h : DrsPreW R b L cost W qp ql qc st up ul uc vp vl vc s) : Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 ∧ Apart up (8 * ul) (s.fsBase.toNat - 8) 8 ∧ Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- the precondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost : Nat) (qp ql qc st up ul uc vp vl vc : Nat)
    (s : State) : Prop :=
  DrsPreW R b L cost 40960 qp ql qc st up ul uc vp vl vc s

/-- the postcondition of `divRecursiveStep` with the stack window `W` (FS base and DF kept) -/
@[reducible] def DrsPostW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost W : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  natVal s'.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl ∧
  natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), EvenHyp.RtPost R b cost L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
    MemFrame s.mem s'.mem (R.rt ++ win s W 96 ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem s'.mem L ([(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs s.mem st)

/-- the postcondition of `divRecursiveStep` (window `40960`) -/
abbrev DrsPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (cost : Nat) (qp ql st up ul vp vl : Nat)
    (s s' : State) : Prop :=
  DrsPostW R b L cost 40960 qp ql st up ul vp vl s s'

/-- `divRecursiveStep`'s `Ensures` (on the division library program; `v`'s words bound by the pre's stack slots) -/
def DrsHyp (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat),
    Ensures ((Extracted.program.onlySegments drsNames).link impl) (segAddr Extracted.program drsFn)
      [qp, ql, qc, st, up, ul, uc, d]
      (fun s => DrsPre R b L (dc (stLen s.mem st.toNat) ul.toNat vl) qp.toNat ql.toNat qc.toNat st.toNat up.toNat
        ul.toNat uc.toNat vp vl vc s)
      (fun s s' => DrsPost R b L (dc (stLen s.mem st.toNat) ul.toNat vl) qp.toNat ql.toNat st.toNat up.toNat
        ul.toNat vp vl s s')

/-! ## `divLarge` -/

/-- the budget of `divLarge` (as arm64): `stk.nat(n)`, `u.make(len uIn + 1)`, `z.make(m + 1)` and the division -/
@[reducible] def cost (dc : Nat → Nat → Nat → Nat) (l il vl : Nat) : Nat :=
  stackNatCost l vl + makeCost (il + 1) + makeCost (il - vl + 1) +
    max (stackNatCost (l + StackNat.rnd vl) (vl + 1)) (dc (l + StackNat.rnd vl) (il + 1) vl)

/-- The precondition (register args `z = (zp, _, zc)`, `st`, `u = (up, _, uc)`; the stack args `uIn = (ip, il, _)` at `RSP + 8, + 16` and `vIn = (vp, vl, _)` at `RSP + 32, + 40`); a plain conjunction (conjuncts in order: ce, sv, gl, zo, uo, io, vo, v2, vil, il9, vn, zu, zio, uv, ui, sti, stl, sz, su, si, svv, wbap, hf, w0, st0, ga, cost, inv, ipS, ilS, vpS, vlS, stt, stft; accessors `Pre.<name>`). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State) :
    Prop :=
  (CallEnv R L s 41272 112) ∧
  (Serves R) ∧
  (RunIface.Globals R s.mem (win s 41272 112)) ∧
  (EvenHyp.WrOut R L s 41272 112 zp zc) ∧
  (EvenHyp.WrOut R L s 41272 112 up uc) ∧
  (EvenHyp.RdIn R L s 41272 112 ip il) ∧
  (EvenHyp.RdIn R L s 41272 112 vp vl) ∧
  (2 ≤ vl) ∧
  (vl ≤ il) ∧
  (il ≤ 2 ^ 9) ∧
  (NatNorm s.mem vp vl) ∧
  (0 < zc → 0 < uc → Apart zp (8 * zc) up (8 * uc)) ∧
  (0 < zc → Apart zp (8 * zc) ip (8 * il) ∧ Apart zp (8 * zc) vp (8 * vl)) ∧
  (0 < uc → Apart up (8 * uc) vp (8 * vl)) ∧
  (up = ip ∨ (0 < uc → Apart up (8 * uc) ip (8 * il))) ∧
  (StkIn R L s 41272 112 st) ∧
  (stLen s.mem st + 16 * il + 64 ≤ 2 ^ 16) ∧
  (0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (0 < uc → Apart up (8 * uc) st 24 ∧ Apart up (8 * uc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart ip (8 * il) st 24 ∧ Apart ip (8 * il) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  (st ≠ 0) ∧
  ((0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < uc → Apart up (8 * uc) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  (c ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = ip) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = il) ∧
  (s.mem.readLE ((s.regs 4).toNat + 32) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl) ∧
  (Apart st 24 (s.fsBase.toNat - 8) 8) ∧
  (Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8)

theorem Pre.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : CallEnv R L s 41272 112 := h.1
theorem Pre.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Serves R := h.2.1
theorem Pre.gl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : RunIface.Globals R s.mem (win s 41272 112) := h.2.2.1
theorem Pre.zo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : EvenHyp.WrOut R L s 41272 112 zp zc := h.2.2.2.1
theorem Pre.uo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : EvenHyp.WrOut R L s 41272 112 up uc := h.2.2.2.2.1
theorem Pre.io {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : EvenHyp.RdIn R L s 41272 112 ip il := h.2.2.2.2.2.1
theorem Pre.vo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : EvenHyp.RdIn R L s 41272 112 vp vl := h.2.2.2.2.2.2.1
theorem Pre.v2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 2 ≤ vl := h.2.2.2.2.2.2.2.1
theorem Pre.vil {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : vl ≤ il := h.2.2.2.2.2.2.2.2.1
theorem Pre.il9 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : il ≤ 2 ^ 9 := h.2.2.2.2.2.2.2.2.2.1
theorem Pre.vn {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : NatNorm s.mem vp vl := h.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 0 < zc → 0 < uc → Apart zp (8 * zc) up (8 * uc) := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zio {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 0 < zc → Apart zp (8 * zc) ip (8 * il) ∧ Apart zp (8 * zc) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 0 < uc → Apart up (8 * uc) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ui {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : up = ip ∨ (0 < uc → Apart up (8 * uc) ip (8 * il)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.sti {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : StkIn R L s 41272 112 st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : stLen s.mem st + 16 * il + 64 ≤ 2 ^ 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.sz {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.su {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : 0 < uc → Apart up (8 * uc) st 24 ∧ Apart up (8 * uc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.si {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart ip (8 * il) st 24 ∧ Apart ip (8 * il) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.svv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.wbap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.hf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.w0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : stCap s.mem st = 0 → stW s.mem st = 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.st0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : st ≠ 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ga {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < uc → Apart up (8 * uc) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : c ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ipS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 8) 8 = ip := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ilS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 16) 8 = il := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vpS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 32) 8 = vp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vlS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stt {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart st 24 (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stft {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- an array's range, empty when `c = 0` (the pointer of a `cap = 0` nat is arbitrary) -/
@[reducible] def ar (p c : Nat) : List (Nat × Nat) := if 0 < c then [(p, p + 8 * c)] else []

/-- The postcondition (as arm64; FS base and DF kept): `q = U / V` (old `z` array or a fresh one) in `RAX, RBX, RCX`,
`r = U mod V` (old `u` array or a fresh one, apart from the stack's final array) in `RDI, RSI, R8`, both normalised;
the stack's `len` restored. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem ip il / natVal s.mem vp vl) ∧
      ExpHyp.NatOF R L L' s'.mem up uc 1 r rl rc (natVal s.mem ip il % natVal s.mem vp vl) ∧
      EvenHyp.RtPost R b c L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = up ∧ rc = uc) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 41272 112 ++ (ar zp zc ++ ar up uc) ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((ar zp zc ++ ar up uc) ++ stkWs s.mem st)

/-- `divLarge`'s `Ensures` with budget bound `cost dc` (`uIn`, `vIn` bound by the pre's stack slots) -/
def Hyp (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (ip il vp vl : Nat),
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, u, ul, uc]
      (fun s => Pre R b L (cost dc (stLen s.mem st.toNat) il vl) z.toNat zc.toNat st.toNat u.toNat uc.toNat
        ip il vp vl s)
      (fun s s' => Post R b L (cost dc (stLen s.mem st.toNat) il vl) z.toNat zc.toNat st.toNat u.toNat
        uc.toNat ip il vp vl s s')

end FvModexp.Amd64.DivLarge
