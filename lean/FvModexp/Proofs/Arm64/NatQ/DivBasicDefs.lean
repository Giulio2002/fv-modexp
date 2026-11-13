import FvModexp.Proofs.Arm64.Nat.DivBasicDefs
import FvModexp.Proofs.Arm64.Nat.StackNatXDefs

set_option autoImplicit false

/-!
# `divBasic` (arm64), Q-form (TIGHT COSTS, asm s38): the statement pieces that carry the budget

Twins of `Pre` / `Post` / `PostL` / `Env` / `RQ` of Arm64/Nat/DivBasicDefs.lean with a reserve level `H`
(Common/StackPot): `Pre`'s cost slot is `(stLen + vl + 4 ≤ H ∧ stkR H s.mem st ≤ b)` (the level twin of `stk.nat(n+1)`'s
bound; consumption `C = 0`: the only charged call is `stk.nat`), the post's budget `b - stkR H s.mem st +
stkR H s'.mem st ≤ b'`, `Env.bud` after `stk.nat` with the capacity `c1`. Everything else is the original's (opened).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic

/-- The precondition (args `q = (qp, ql, _)`, `st`, `u = (up, ul, _)`, `v = (vp, vl, _)`); a plain conjunction (Janus' audit
accepts only plain defs in statements); conjuncts in order: ce, sv, wbacc, wbap, v2, vtop, vacc, v48, vh, vw, ub, ulc, ucb, uacc, u48, uh, uw, ug, qb, qacc, q48, qh, qw, qg, qu, qv, uv, room, stok, stw, stg, starr, stgf, stlen, stq, stu, stv, free, stfree, stfw, cost, inv (accessors `Pre.<name>`). -/
def Pre (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State) : Prop :=
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
  (stLen s.mem st + vl + 4 ≤ H ∧ stkR H s.mem st ≤ b) ∧
  (R.inv b L (s.regs 28).toNat (view R.rt L s.mem))

theorem Pre.ce {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : CallEnv R L s 4464 88 := h.1
theorem Pre.sv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Serves R := h.2.1
theorem Pre.wbacc {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : s.mem.accessible StackNat.wbA 4 false = true := h.2.2.1
theorem Pre.wbap {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.1
theorem Pre.v2 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : 2 ≤ vl := h.2.2.2.2.1
theorem Pre.vtop {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : 2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8 := h.2.2.2.2.2.1
theorem Pre.vacc {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : s.mem.accessible vp (8 * vl) false = true := h.2.2.2.2.2.2.1
theorem Pre.v48 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : vp + 8 * vl ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.1
theorem Pre.vh {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Held R L vp (8 * vl) := h.2.2.2.2.2.2.2.2.1
theorem Pre.vw {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Outside vp (8 * vl) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.1
theorem Pre.ub {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : ul < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ulc {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : ul ≤ uc := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ucb {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : uc < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uacc {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : s.mem.accessible up (8 * ul) true = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.u48 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : up + 8 * ul ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uh {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Held R L up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uw {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Outside up (8 * ul) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ug {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart up (8 * ul) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qb {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : ql < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qacc {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : s.mem.accessible qp (8 * ql) true = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.q48 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : qp + 8 * ql ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qh {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Held R L qp (8 * ql) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qw {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Outside qp (8 * ql) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qg {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qu {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart up (8 * ul) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.room {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : vl ≤ ul → (ul - vl < ql ∨ (ul - vl = ql ∧ natVal s.mem up ul < natVal s.mem vp vl * 2 ^ (64 * ql))) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stok {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : StkOK s.mem R L st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stw {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Outside st 24 (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stg {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.starr {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4464 88) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stgf {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 28).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stlen {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : stLen s.mem st + vl + 4 ≤ 2 ^ 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stq {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 qp (8 * ql) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stu {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 up (8 * ul) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.free {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) (freeP s.mem st) (freeN s.mem st) ∧ Apart up (8 * ul) (freeP s.mem st) (freeN s.mem st) ∧ Apart vp (8 * vl) (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfree {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Apart st 24 (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfw {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : Outside (freeP s.mem st) (freeN s.mem st) (win s 4464 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : stLen s.mem st + vl + 4 ≤ H ∧ stkR H s.mem st ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b H L qp ql st up ul uc vp vl s) : R.inv b L (s.regs 28).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The postcondition: `q[0 : qn]` holds `U / V` (for `len v ≤ len u`; `qn = len q` only when the top digit is 0) and
`u` holds `U mod V` in place; the rest of `q` is untouched (frame). -/
@[reducible] def Post (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - stkR H s.mem st + stkR H s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4464 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

/-- `Post` with `StackBackL` (STACK-IN-LIVE-SET decision): a grown stack array is an element of `L'`, `0 < cap` -/
@[reducible] def PostL (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - stkR H s.mem st + stkR H s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4464 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

theorem PostL.toPost {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {qp ql st up ul vp vl : Nat} {s s' : State}
    (h : PostL R b H L qp ql st up ul vp vl s s') : Post R b H L qp ql st up ul vp vl s s' := by
  obtain ⟨h1, h2, L', b', h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, L', b', h3, h4, h5, h6.1, h7, h8⟩

/-- the facts fixed from the `stk.nat` call on: the scratch `qhatv` at `t` (`n + 1` words), the live set `L1`, the
budget `b1`, the stack array `(w1, c1)`. -/
structure Env (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b H L qp ql st up ul uc vp vl s
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t (vl + 1)
  ext : LiveExt R L L1
  bud : b - stkR H s.mem st + (stkRes H - potK * c1) ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1
  arrL : ¬(w1 = stW s.mem st ∧ c1 = stCap s.mem st) → (w1, w1 + 8 * c1) ∈ L1 ∧ 0 < c1

/-- what every segment lemma concludes (registers kept + `Post`) -/
@[reducible] def RQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    PostL R b H L qp ql st up ul vp vl s s'

end FvModexp.Arm64.Q.DivBasic
