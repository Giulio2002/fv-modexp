import FvModexp.Proofs.Amd64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Amd64.NatQ.DivBasic

set_option autoImplicit false

/-!
# `divLarge` (amd64), Q-form (TIGHT COSTS, top s38): `Q.DivLarge.Pre` / `Post` / `Hyp`

Amd64 twin of Arm64/NatQ/DivLargeDefs.lean (asm s38): the statement of Amd64/Nat/DivLargeDefs.lean with a reserve level
`H` and the level-free cost `Q.DivLarge.costQ dc il vl` (NatQ/DivHypQ.lean): `Pre`'s cost slot is
`(stLen + 16·il + 64 ≤ H ∧ c + stkR H s.mem st ≤ b)`, `Post`'s `RtPost … c` is `RtPostQ … (c + stkR H s.mem st)
(stkR H s'.mem st)`; `divRecursiveStep` is the premise `DrsHypQ` (NatQ/DrsIfaceQ.lean). Everything else verbatim.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge

/-- The precondition (register args `z = (zp, _, zc)`, `st`, `u = (up, _, uc)`; the stack args `uIn = (ip, il, _)` at `RSP + 8, + 16` and `vIn = (vp, vl, _)` at `RSP + 32, + 40`); a plain conjunction (conjuncts in order: ce, sv, gl, zo, uo, io, vo, v2, vil, il9, vn, zu, zio, uv, ui, sti, stl, sz, su, si, svv, wbap, hf, w0, st0, ga, cost, inv, ipS, ilS, vpS, vlS, stt, stft, adx, ta; accessors `Pre.<name>`). -/
def Pre (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State) :
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
  (stLen s.mem st + 16 * il + 64 ≤ H ∧ c + stkR H s.mem st ≤ b) ∧
  (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = ip) ∧
  (s.mem.readLE ((s.regs 4).toNat + 16) 8 = il) ∧
  (s.mem.readLE ((s.regs 4).toNat + 32) 8 = vp) ∧
  (s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl) ∧
  (Apart st 24 (s.fsBase.toNat - 8) 8) ∧
  (Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8) ∧
  (s.mem.accessible Callees.adxAddr 1 false = true) ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8)

theorem Pre.ce {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : CallEnv R L s 41272 112 := h.1
theorem Pre.sv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Serves R := h.2.1
theorem Pre.gl {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : RunIface.Globals R s.mem (win s 41272 112) := h.2.2.1
theorem Pre.zo {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : EvenHyp.WrOut R L s 41272 112 zp zc := h.2.2.2.1
theorem Pre.uo {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : EvenHyp.WrOut R L s 41272 112 up uc := h.2.2.2.2.1
theorem Pre.io {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : EvenHyp.RdIn R L s 41272 112 ip il := h.2.2.2.2.2.1
theorem Pre.vo {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : EvenHyp.RdIn R L s 41272 112 vp vl := h.2.2.2.2.2.2.1
theorem Pre.v2 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 2 ≤ vl := h.2.2.2.2.2.2.2.1
theorem Pre.vil {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : vl ≤ il := h.2.2.2.2.2.2.2.2.1
theorem Pre.il9 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : il ≤ 2 ^ 9 := h.2.2.2.2.2.2.2.2.2.1
theorem Pre.vn {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : NatNorm s.mem vp vl := h.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zu {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < zc → 0 < uc → Apart zp (8 * zc) up (8 * uc) := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zio {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < zc → Apart zp (8 * zc) ip (8 * il) ∧ Apart zp (8 * zc) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.uv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < uc → Apart up (8 * uc) vp (8 * vl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ui {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : up = ip ∨ (0 < uc → Apart up (8 * uc) ip (8 * il)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.sti {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : StkIn R L s 41272 112 st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stl {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : stLen s.mem st + 16 * il + 64 ≤ 2 ^ 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.sz {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.su {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < uc → Apart up (8 * uc) st 24 ∧ Apart up (8 * uc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.si {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart ip (8 * il) st 24 ∧ Apart ip (8 * il) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.svv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.wbap {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.hf {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.w0 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : stCap s.mem st = 0 → stW s.mem st = 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.st0 {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : st ≠ 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ga {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < uc → Apart up (8 * uc) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧ Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : c + stkR H s.mem st ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
theorem Pre.lvH {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : stLen s.mem st + 16 * il + 64 ≤ H := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
theorem Pre.inv {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ipS {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 8) 8 = ip := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.ilS {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 16) 8 = il := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vpS {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 32) 8 = vp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.vlS {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stt {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart st 24 (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stft {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.adx {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : s.mem.accessible Callees.adxAddr 1 false = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pre.ta {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b H L c zp zc st up uc ip il vp vl s) : 0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The postcondition (as arm64; FS base and DF kept): `q = U / V` (old `z` array or a fresh one) in `RAX, RBX, RCX`,
`r = U mod V` (old `u` array or a fresh one, apart from the stack's final array) in `RDI, RSI, R8`, both normalised;
the stack's `len` restored. -/
@[reducible] def Post (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem ip il / natVal s.mem vp vl) ∧
      ExpHyp.NatOF R L L' s'.mem up uc 1 r rl rc (natVal s.mem ip il % natVal s.mem vp vl) ∧
      RtPostQ R b (c + stkR H s.mem st) (stkR H s'.mem st) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = up ∧ rc = uc) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 41272 112 ++ (ar zp zc ++ ar up uc) ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((ar zp zc ++ ar up uc) ++ stkWs s.mem st)

/-- `divLarge`'s `Ensures` with budget bound `costQ dc` (Q-form) (`uIn`, `vIn` bound by the pre's stack slots) -/
def Hyp (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (ip il vp vl : Nat),
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, u, ul, uc]
      (fun s => Pre R b H L (costQ dc il vl) z.toNat zc.toNat st.toNat u.toNat uc.toNat
        ip il vp vl s)
      (fun s s' => Post R b H L (costQ dc il vl) z.toNat zc.toNat st.toNat u.toNat
        uc.toNat ip il vp vl s s')


end FvModexp.Amd64.Q.DivLarge
