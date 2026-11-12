import FvModexp.Proofs.Arm64.Nat.LibDivBasic
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Arm64.Nat.Restore
import FvModexp.Proofs.Arm64.Exp.ExpHyp
import FvModexp.Proofs.Arm64.DivWWSum
import FvModexp.Proofs.Arm64.RecipWordSum
import FvModexp.Proofs.Arm64.MulAddVWWSum
import FvModexp.Proofs.Common.DivBasic
import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.DivBasicMem

set_option autoImplicit false

/-!
# `(q nat) divBasic(stk *stack, u, v nat)` (go-bigmodexpfix natdiv.go:646), arm64 — statement and segment relations

Knuth's algorithm D (model `Mdl.divBasic` / `dbLoop` / `dbStep`, Common/DivBasic.lean; contract `Mdl.divBasic_contract`).
Args `X0..X2 = q`, `X3 = stk`, `X4..X6 = u`, `X7..X9 = v`. Frame 240 (`MOVD.W R30, -240(RSP)`, `SP' = SP - 240`), spills
`q.ptr, q.len` at `SP + 8, SP + 16`, `u` at `SP + 40 … SP + 56`, `v` at `SP + 64 … SP + 80` (`above = 88`); deepest
callee `(*stack).nat` (`stkSN ≤ 4224` below `SP'`): `stk = 240 + 4224 = 4464`.
Locals (offsets from the ENTRY `SP`): saved LR `-240`, saved FP `-248`, ABI0 argument area `[-232, -160)`, defer bit
`-137`, `vn1` `-136`, `rec` `-128`, `qhl` `-120`, `qhatv` len/cap `-112`, `-104`, `qhat` `-96`, `m` `-88`, `j` `-80`,
`j+n` `-72`, scratch `-64`, `qhatv` ptr `-56`, `&u[j]` `-48`, defer record `{deferwrap1, stk, len(stk.w)}` at
`-40, -32, -24`, its address at `-16`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.DivBasic

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic"
def names : List String := LibDivBasic.names

/-- the free part of the stack array -/
@[reducible] def freeP (m : Memory) (st : Nat) : Nat := stW m st + 8 * stLen m st
@[reducible] def freeN (m : Memory) (st : Nat) : Nat := 8 * (stCap m st - stLen m st)

/-- the model's lists: `q`, `u`, `v` as limb lists of the entry memory -/
@[reducible] def lq (m : Memory) (qp ql : Nat) : List Nat := Asm.limbs m qp ql

/-- The precondition (args `q = (qp, ql, _)`, `st`, `u = (up, ul, _)`, `v = (vp, vl, _)`); a plain conjunction (Janus' audit
accepts only plain defs in statements); conjuncts in order: ce, sv, wbacc, wbap, v2, vtop, vacc, v48, vh, vw, ub, ulc, ucb, uacc, u48, uh, uw, ug, qb, qacc, q48, qh, qw, qg, qu, qv, uv, room, stok, stw, stg, starr, stgf, stlen, stq, stu, stv, free, stfree, stfw, cost, inv (accessors `Pre.<name>`). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State) : Prop :=
  (CallEnv R L s 4464 88) ∧
  (Serves R) ∧
  (s.mem.accessible StackNat.wbA 4 false = true) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (2 ≤ vl) ∧
  (2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true) ∧
  (vp + 8 * vl ≤ 2 ^ 48) ∧
  (Held R L vp (8 * vl)) ∧
  (Outside vp (8 * vl) (win s 4464 88)) ∧
  (ul < 2 ^ 40) ∧
  (ul ≤ uc) ∧
  (uc < 2 ^ 40) ∧
  (s.mem.accessible up (8 * ul) true = true) ∧
  (up + 8 * ul ≤ 2 ^ 48) ∧
  (Held R L up (8 * ul)) ∧
  (Outside up (8 * ul) (win s 4464 88)) ∧
  (Apart up (8 * ul) ((s.regs 28).toNat + 16) 8) ∧
  (ql < 2 ^ 40) ∧
  (s.mem.accessible qp (8 * ql) true = true) ∧
  (qp + 8 * ql ≤ 2 ^ 48) ∧
  (Held R L qp (8 * ql)) ∧
  (Outside qp (8 * ql) (win s 4464 88)) ∧
  (Apart qp (8 * ql) ((s.regs 28).toNat + 16) 8) ∧
  (Apart qp (8 * ql) up (8 * ul)) ∧
  (Apart qp (8 * ql) vp (8 * vl)) ∧
  (Apart up (8 * ul) vp (8 * vl)) ∧
  (vl ≤ ul → (ul - vl < ql ∨ (ul - vl = ql ∧ natVal s.mem up ul < natVal s.mem vp vl * 2 ^ (64 * ql)))) ∧
  (StkOK s.mem R L st) ∧
  (Outside st 24 (win s 4464 88)) ∧
  (Apart st 24 ((s.regs 28).toNat + 16) 8) ∧
  (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4464 88) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
  (Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 28).toNat + 16) 8) ∧
  (stLen s.mem st + vl + 4 ≤ 2 ^ 16) ∧
  (Apart st 24 qp (8 * ql)) ∧
  (Apart st 24 up (8 * ul)) ∧
  (Apart st 24 vp (8 * vl)) ∧
  (Apart qp (8 * ql) (freeP s.mem st) (freeN s.mem st) ∧ Apart up (8 * ul) (freeP s.mem st) (freeN s.mem st) ∧ Apart vp (8 * vl) (freeP s.mem st) (freeN s.mem st)) ∧
  (Apart st 24 (freeP s.mem st) (freeN s.mem st)) ∧
  (Outside (freeP s.mem st) (freeN s.mem st) (win s 4464 88)) ∧
  (ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b) ∧
  (R.inv b L (s.regs 28).toNat (view R.rt L s.mem))

theorem Pre.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : CallEnv R L s 4464 88 := h.1
theorem Pre.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Serves R := h.2.1
theorem Pre.wbacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.accessible StackNat.wbA 4 false = true := h.2.2.1
theorem Pre.wbap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.1
theorem Pre.v2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : 2 ≤ vl := h.2.2.2.2.1
theorem Pre.vtop {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 := h.2.2.2.2.2.1
theorem Pre.vacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.accessible vp (8 * vl) false = true := h.2.2.2.2.2.2.1
theorem Pre.v48 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : vp + 8 * vl ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.1
theorem Pre.vh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Held R L vp (8 * vl) := h.2.2.2.2.2.2.2.2.1
theorem Pre.vw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside vp (8 * vl) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.1
theorem Pre.ub {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : ul < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ulc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : ul ≤ uc := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ucb {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : uc < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.accessible up (8 * ul) true = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.u48 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : up + 8 * ul ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Held R L up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside up (8 * ul) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ug {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart up (8 * ul) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qb {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : ql < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.accessible qp (8 * ql) true = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.q48 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : qp + 8 * ql ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Held R L qp (8 * ql) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside qp (8 * ql) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart up (8 * ul) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.room {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : vl ≤ ul → (ul - vl < ql ∨ (ul - vl = ql ∧ natVal s.mem up ul < natVal s.mem vp vl * 2 ^ (64 * ql))) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stok {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : StkOK s.mem R L st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside st 24 (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.starr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4464 88) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stgf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stlen {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : stLen s.mem st + vl + 4 ≤ 2 ^ 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stq {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 qp (8 * ql) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.free {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) (freeP s.mem st) (freeN s.mem st) ∧ Apart up (8 * ul) (freeP s.mem st) (freeN s.mem st) ∧ Apart vp (8 * vl) (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfree {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside (freeP s.mem st) (freeN s.mem st) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : R.inv b L (s.regs 28).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- the number of quotient words written: `len u - len v + 1` (or `len q` when the top digit has no room), none when
`len u < len v` -/
@[reducible] def qn (ql ul vl : Nat) : Nat := if vl ≤ ul then min (ul - vl + 1) ql else 0

/-- The writes a caller sees: `q[0 : qn]`, `u`, the stack header and the free part of the stack array. -/
@[reducible] def ws (m : Memory) (qp ql st up ul vl : Nat) : List (Nat × Nat) :=
  (qp, qp + 8 * qn ql ul vl) :: (up, up + 8 * ul) :: stkWs m st

/-- The postcondition: `q[0 : qn]` holds `U / V` (for `len v ≤ len u`; `qn = len q` only when the top digit is 0) and
`u` holds `U mod V` in place; the rest of `q` is untouched (frame). -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4464 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

/-- `Post` with `StackBackL` (STACK-IN-LIVE-SET decision): a grown stack array is an element of `L'`, `0 < cap` -/
@[reducible] def PostL (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4464 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

theorem PostL.toPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul vp vl : Nat} {s s' : State}
    (h : PostL R b L qp ql st up ul vp vl s s') : Post R b L qp ql st up ul vp vl s s' := by
  obtain ⟨h1, h2, L', b', h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, L', b', h3, h4, h5, h6.1, h7, h8⟩

/-! ## After `qhatv := stk.nat(n + 1)` -/

/-- the address of the closure `nat.divBasic.deferwrap1` (`ADRP 4096(PC); ADD $848`) -/
abbrev dfnA : Nat := 1811280

/-- the facts fixed from the `stk.nat` call on: the scratch `qhatv` at `t` (`n + 1` words), the live set `L1`, the
budget `b1`, the stack array `(w1, c1)`. -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L qp ql st up ul uc vp vl s
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t (vl + 1)
  ext : LiveExt R L L1
  bud : b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1
  arrL : ¬(w1 = stW s.mem st ∧ c1 = stCap s.mem st) → (w1, w1 + 8 * c1) ∈ L1 ∧ 0 < c1

/-- the ranges written after the `stk.nat` call: `q[0:qn]`, `u`, `qhatv` -/
@[reducible] def wsL (qp ql up ul vl t : Nat) : List (Nat × Nat) :=
  [(qp, qp + 8 * qn ql ul vl), (up, up + 8 * ul), (t, t + 8 * (vl + 1))]

/-- the memory facts at every point after the `reciprocalWord` call (memory `M`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M : Memory) : Prop where
  lr : M.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  dbit : M.readLE (s.sp.toNat - 137) 1 = 1
  vn1 : M.readLE (s.sp.toNat - 136) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  rw : M.readLE (s.sp.toNat - 128) 8 = AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8)
  hl : M.readLE (s.sp.toNat - 112) 8 = vl + 1
  hc : M.readLE (s.sp.toNat - 104) 8 = vl + 1
  mm : M.readLE (s.sp.toNat - 88) 8 = (ul + 2 ^ 64 - vl) % 2 ^ 64
  tp : M.readLE (s.sp.toNat - 56) 8 = t
  dfn : M.readLE (s.sp.toNat - 40) 8 = dfnA
  dst : M.readLE (s.sp.toNat - 32) 8 = st
  dn : M.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : M.readLE (s.sp.toNat + 8) 8 = qp
  s2 : M.readLE (s.sp.toNat + 16) 8 = ql
  s4 : M.readLE (s.sp.toNat + 40) 8 = up
  s5 : M.readLE (s.sp.toNat + 48) 8 = ul
  s6 : M.readLE (s.sp.toNat + 56) 8 = uc
  s7 : M.readLE (s.sp.toNat + 64) 8 = vp
  s8 : M.readLE (s.sp.toNat + 72) 8 = vl
  s9 : M.readLE (s.sp.toNat + 80) 8 = vc
  hw : M.readLE st 8 = w1
  hlen : M.readLE (st + 8) 8 = stLen s.mem st + (vl + 1 + 3) / 4 * 4
  hcap : M.readLE (st + 16) 8 = c1
  vs : ∀ a n, vp ≤ a → a + n ≤ vp + 8 * vl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ winA s 4464 88 ++ wsL qp ql up ul vl t ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (wsL qp ql up ul vl t ++ stkWs s.mem st)
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M)

/-- the loop head (`TBNZ $63, R1`; `R1 = j`, `R2 = ujn`, `R0 = rec`) -/
abbrev head : Nat := segAddr Extracted.program fn + 0xcc

/-- the model lists of the entry memory -/
@[reducible] def V0 (s : State) (vp vl : Nat) : List Nat := Asm.limbs s.mem vp vl

/-- the loop invariant at the head with `k = j + 1` iterations left (memory `M`, `ujn`): Knuth D's `DbInv` on the
limb lists of `q` and `u` -/
@[reducible] def Inv (qp ql up ul vp vl : Nat) (s : State) (k ujn : Nat) (M : Memory) : Prop :=
  Mdl.DbInv (Asm.limbs s.mem vp vl) (Asm.limbs s.mem up ul) (Asm.limbs s.mem qp ql) (ul - vl) k
    (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn

/-- what every segment lemma concludes (registers kept + `Post`) -/
@[reducible] def RQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    PostL R b L qp ql st up ul vp vl s s'

end FvModexp.Arm64.DivBasic
