import FvModexp.Proofs.Amd64.Nat.LibDivBasic
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Amd64.DivWWSum
import FvModexp.Proofs.Amd64.MulAddVWWSum
import FvModexp.Proofs.Common.DivBasic
import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.DivBasicMem

set_option autoImplicit false

/-!
# `(q nat) divBasic(stk *stack, u, v nat)` (go-bigmodexpfix natdiv.go:646), amd64 — statement and segment relations

The amd64 twin of `Arm64/Nat/DivBasicDefs.lean` (agent asm; same model `Mdl.divBasic` / `dbLoop` / `dbStep`,
Common/DivBasic.lean). Go ABIInternal: `RAX, RBX, RCX = q`, `RDI = stk`, `RSI, R8, R9 = u`; `v` does not fit in the
nine integer argument registers and is passed ON THE STACK at `RSP + 8, + 16, + 24` (ptr, len, cap). Frame:
`PUSHQ BP; SUBQ $0xd8, SP` (`SP' = RSP - 224`); spills `q.ptr, q.len` at `RSP + 32, + 40`, `u` at `RSP + 64 … + 80`
(`above = 88`); deepest callee `(*stack).nat` (`CallEnv 4192 24`, entry `RSP - 232`): `stk = 232 + 4192 = 4424`.
`reciprocalWord` is INLINED (`BSRQ … DIVQ`), `divWW` is a Go call (registers).
Locals (offsets from the ENTRY `RSP`): saved `RBP` `-8`, the defer record `{deferwrap1, stk, len(stk.w)}` at
`-40, -32, -24`, its address at `-16`, `&u[j]` `-48`, `qhatv` ptr `-56`, `qhatv` cap (first `n - 1`) `-64`, `vn1` `-72`,
`cap(u) - j` `-80`, `j + n` `-88`, `j` `-96`, `m` `-104`, `qhat` `-112`, `qhatv` len `-120`, `qhl` `-128`, `rec` `-136`,
the defer bit (byte) `-137`; the ABI0 argument area `[RSP - 224, RSP - 144)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.DivBasic

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic"
def names : List String := LibDivBasic.names

/-- the free part of the stack array -/
@[reducible] def freeP (m : Memory) (st : Nat) : Nat := stW m st + 8 * stLen m st
@[reducible] def freeN (m : Memory) (st : Nat) : Nat := 8 * (stCap m st - stLen m st)

/-- The precondition (register args `q = (qp, ql, _)`, `st`, `u = (up, ul, uc)`; the stack args `v = (vp, vl, _)` at `RSP + 8`, `RSP + 16`); a plain conjunction (Janus' audit accepts only plain defs in statements) (conjuncts in order: ce, sv, wbacc, wbap, v2, vtop, vacc, v48, vh, vw, ub, ulc, ucb, uacc, u48, uh, uw, ug, qb, qacc, q48, qh, qw, qg, qu, qv, uv, room, stok, stw, stg, starr, stgf, stlen, stq, stu, stv, free, stfree, stfw, cost, inv, vpS, vlS, qt, ut, stt, stft; accessors `Pre.<name>`). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State) : Prop :=
  (CallEnv R L s 4424 88) ∧
  (Serves R) ∧
  (s.mem.accessible StackNat.wbA 4 false = true) ∧
  (Apart st 24 StackNat.wbA 4) ∧
  (2 ≤ vl) ∧
  (2 ^ 63 ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) ∧
  (s.mem.accessible vp (8 * vl) false = true) ∧
  (vp + 8 * vl ≤ 2 ^ 48) ∧
  (Held R L vp (8 * vl)) ∧
  (Outside vp (8 * vl) (win s 4424 88)) ∧
  (ul < 2 ^ 40) ∧
  (ul ≤ uc) ∧
  (uc < 2 ^ 40) ∧
  (s.mem.accessible up (8 * ul) true = true) ∧
  (up + 8 * ul ≤ 2 ^ 48) ∧
  (Held R L up (8 * ul)) ∧
  (Outside up (8 * ul) (win s 4424 88)) ∧
  (Apart up (8 * ul) ((s.regs 14).toNat + 16) 8) ∧
  (ql < 2 ^ 40) ∧
  (s.mem.accessible qp (8 * ql) true = true) ∧
  (qp + 8 * ql ≤ 2 ^ 48) ∧
  (Held R L qp (8 * ql)) ∧
  (Outside qp (8 * ql) (win s 4424 88)) ∧
  (Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8) ∧
  (Apart qp (8 * ql) up (8 * ul)) ∧
  (Apart qp (8 * ql) vp (8 * vl)) ∧
  (Apart up (8 * ul) vp (8 * vl)) ∧
  (vl ≤ ul → (ul - vl < ql ∨ (ul - vl = ql ∧ natVal s.mem up ul < natVal s.mem vp vl * 2 ^ (64 * ql)))) ∧
  (StkOK s.mem R L st) ∧
  (Outside st 24 (win s 4424 88)) ∧
  (Apart st 24 ((s.regs 14).toNat + 16) 8) ∧
  (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4424 88) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
  (Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 14).toNat + 16) 8) ∧
  (stLen s.mem st + vl + 4 ≤ 2 ^ 16) ∧
  (Apart st 24 qp (8 * ql)) ∧
  (Apart st 24 up (8 * ul)) ∧
  (Apart st 24 vp (8 * vl)) ∧
  (Apart qp (8 * ql) (freeP s.mem st) (freeN s.mem st) ∧ Apart up (8 * ul) (freeP s.mem st) (freeN s.mem st) ∧ Apart vp (8 * vl) (freeP s.mem st) (freeN s.mem st)) ∧
  (Apart st 24 (freeP s.mem st) (freeN s.mem st)) ∧
  (Outside (freeP s.mem st) (freeN s.mem st) (win s 4424 88)) ∧
  (stackNatCost (stLen s.mem st) (vl + 1) ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl) ∧
  (Apart qp (8 * ql) (s.fsBase.toNat - 8) 8) ∧
  (Apart up (8 * ul) (s.fsBase.toNat - 8) 8) ∧
  (Apart st 24 (s.fsBase.toNat - 8) 8) ∧
  (Apart (freeP s.mem st) (freeN s.mem st) (s.fsBase.toNat - 8) 8)

theorem Pre.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : CallEnv R L s 4424 88 := h.1
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
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside vp (8 * vl) (win s 4424 88) := h.2.2.2.2.2.2.2.2.2.1
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
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside up (8 * ul) (win s 4424 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ug {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart up (8 * ul) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qb {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : ql < 2 ^ 40 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.accessible qp (8 * ql) true = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.q48 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : qp + 8 * ql ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Held R L qp (8 * ql) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside qp (8 * ql) (win s 4424 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside st 24 (win s 4424 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.starr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4424 88) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stgf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
    (h : Pre R b L qp ql st up ul uc vp vl s) : Outside (freeP s.mem st) (freeN s.mem st) (win s 4424 88) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : stackNatCost (stLen s.mem st) (vl + 1) ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vpS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vlS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.qt {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart qp (8 * ql) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ut {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart up (8 * ul) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stt {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart st 24 (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stft {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (h : Pre R b L qp ql st up ul uc vp vl s) : Apart (freeP s.mem st) (freeN s.mem st) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- the number of quotient words written: `len u - len v + 1` (or `len q` when the top digit has no room), none when
`len u < len v` -/
@[reducible] def qn (ql ul vl : Nat) : Nat := if vl ≤ ul then min (ul - vl + 1) ql else 0

/-- The writes a caller sees: `q[0 : qn]`, `u`, the stack header and the free part of the stack array. -/
@[reducible] def ws (m : Memory) (qp ql st up ul vl : Nat) : List (Nat × Nat) :=
  (qp, qp + 8 * qn ql ul vl) :: (up, up + 8 * ul) :: stkWs m st

/-- The postcondition (`StackBackL`): `q[0 : qn]` holds `U / V` (for `len v ≤ len u`) and `u` holds `U mod V` in place;
FS base and DF kept (AMD64 DF CONVENTION). -/
@[reducible] def PostL (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) (vl + 1) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4424 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

/-- `PostL` with `StackBack` -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  (vl ≤ ul → natVal s'.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl) ∧
    natVal s'.mem up ul = natVal s.mem up ul % natVal s.mem vp vl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) (vl + 1) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4424 88 ++ ws s.mem qp ql st up ul vl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem qp ql st up ul vl)

theorem PostL.toPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul vp vl : Nat} {s s' : State}
    (h : PostL R b L qp ql st up ul vp vl s s') : Post R b L qp ql st up ul vp vl s s' := by
  obtain ⟨h0, h0', h1, h2, L', b', h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h0, h0', h1, h2, L', b', h3, h4, h5, h6.1, h7, h8⟩

/-- The register part of the postcondition (what `Ensures.toSummaryIn` keeps). -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

/-- what every segment lemma concludes (registers kept + `PostL`) -/
@[reducible] def RQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul vp vl : Nat) (s s' : State) : Prop :=
  RegsOK s s' ∧ PostL R b L qp ql st up ul vp vl s s'

/-! ## After `qhatv := stk.nat(n + 1)` -/

/-- the address of the closure `nat.divBasic.deferwrap1` (`LEAQ …(SB), SI` at `+0x75`) -/
abbrev dfnA : Nat := 6223936

/-- the facts fixed from the `stk.nat` call on (as the arm64 twin), plus the entry's `X15`, `DF` and return address -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L qp ql st up ul uc vp vl s
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t (vl + 1)
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) (vl + 1) ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1
  arrL : ¬(w1 = stW s.mem st ∧ c1 = stCap s.mem st) → (w1, w1 + 8 * c1) ∈ L1 ∧ 0 < c1
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  ra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- the ranges written after the `stk.nat` call: `q[0:qn]`, `u`, `qhatv` -/
@[reducible] def wsL (qp ql up ul vl t : Nat) : List (Nat × Nat) :=
  [(qp, qp + 8 * qn ql ul vl), (up, up + 8 * ul), (t, t + 8 * (vl + 1))]

/-- the memory facts at every point after the inlined `reciprocalWord` (memory `M`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M : Memory) : Prop where
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : M.readLE ((s.regs 4).toNat - 137) 1 = 1
  rw : M.readLE ((s.regs 4).toNat - 136) 8 = AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8)
  hl : M.readLE ((s.regs 4).toNat - 120) 8 = vl + 1
  mm : M.readLE ((s.regs 4).toNat - 104) 8 = (ul + 2 ^ 64 - vl) % 2 ^ 64
  vn1 : M.readLE ((s.regs 4).toNat - 72) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  hc : M.readLE ((s.regs 4).toNat - 64) 8 = vl + 1
  tp : M.readLE ((s.regs 4).toNat - 56) 8 = t
  dfn : M.readLE ((s.regs 4).toNat - 40) 8 = dfnA
  dst : M.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : M.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s7 : M.readLE ((s.regs 4).toNat + 8) 8 = vp
  s8 : M.readLE ((s.regs 4).toNat + 16) 8 = vl
  s9 : M.readLE ((s.regs 4).toNat + 24) 8 = vc
  s1 : M.readLE ((s.regs 4).toNat + 32) 8 = qp
  s2 : M.readLE ((s.regs 4).toNat + 40) 8 = ql
  s4 : M.readLE ((s.regs 4).toNat + 64) 8 = up
  s5 : M.readLE ((s.regs 4).toNat + 72) 8 = ul
  s6 : M.readLE ((s.regs 4).toNat + 80) 8 = uc
  hw : M.readLE st 8 = w1
  hlen : M.readLE (st + 8) 8 = stLen s.mem st + (vl + 1 + 3) / 4 * 4
  hcap : M.readLE (st + 16) 8 = c1
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  vs : ∀ a n, vp ≤ a → a + n ≤ vp + 8 * vl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ win s 4424 88 ++ wsL qp ql up ul vl t ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (wsL qp ql up ul vl t ++ stkWs s.mem st)
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M)

/-- the loop head (`TESTQ DX, DX; JL exit`; `RDX = j`, `R8 = ujn`, `RAX = rec`, `RCX = n`, `RBX = len qhatv`,
`RSI = v.ptr`, `RDI = cap qhatv`, `R10 = qhatv.ptr`, `R11 = vn1`) -/
abbrev head : Nat := segAddr Extracted.program fn + 0x1a1

/-- the loop invariant at the head with `k = j + 1` iterations left (memory `M`, `ujn`): Knuth D's `DbInv` on the
limb lists of `q` and `u` -/
@[reducible] def Inv (qp ql up ul vp vl : Nat) (s : State) (k ujn : Nat) (M : Memory) : Prop :=
  Mdl.DbInv (Asm.limbs s.mem vp vl) (Asm.limbs s.mem up ul) (Asm.limbs s.mem qp ql) (ul - vl) k
    (Asm.limbs M qp ql) (Asm.limbs M up ul) ujn

end FvModexp.Amd64.DivBasic
