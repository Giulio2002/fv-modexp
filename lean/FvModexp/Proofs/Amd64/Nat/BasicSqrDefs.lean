import FvModexp.Proofs.Amd64.Nat.LibBasicSqr
import FvModexp.Proofs.Amd64.Nat.BasicMul
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.SqrMath

/-!
# `basicSqr(stk, z, x nat)` (go-bigmodexpfix natmul.go:113), amd64 — statement and the relations between segments

The amd64 twin of `Arm64/Nat/BasicSqrDefs.lean` (Go source there). Args `RAX = stk`, `RBX, RCX, RDI = z`,
`RSI, R8, R9 = x`. Frame: `PUSHQ BP; SUBQ $0xb8, SP` (`SP' = RSP - 192`); the spills of `z`, `x` at `RSP + 16 … RSP + 64`
(`above = 64`); deepest callee `basicMul` (`CallEnv 4224 72`, entry `RSP - 200`): `stk = 200 + 4224 = 4424`.
Locals (offsets from the entry `RSP`): saved `RBP` at `-8`; `t` at `-48` (ptr), `-88` (len), `-80` (cap); the loop
scratch `16i, 2i, i` at `-72, -64, -56`; the defer record `{deferwrap1, stk, len(stk.w)}` at `-40, -32, -24`, its
address at `-16`, the defer bit at `-89`; the ABI0 argument area `[RSP - 192, RSP - 96)`.

The result: `z[0:2n] = x²`; the stack comes back with its `len` (`StackBackL`: a grown array is in the live set).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.BasicSqr

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr"
def names : List String := LibBasicSqr.names

/-- `basicSqrThreshold` (natmul.go:68, a writable global) -/
abbrev thrA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold»

/-- the free part of the stack array -/
@[reducible] def freeP (m : Memory) (st : Nat) : Nat := stW m st + 8 * stLen m st
@[reducible] def freeN (m : Memory) (st : Nat) : Nat := 8 * (stCap m st - stLen m st)

/-- The precondition (args `st`, `z = (zp, zl, zc)`, `x = (xp, xl, _)`), a plain conjunction (Janus' audit accepts only
plain defs in statements); the conjuncts in order: ce, sv, thA, thV, thO, x0, zl2, zlc, zcb, zlive, zw, zg, zt, xacc, x48, xh, xw, zx, stok, stw, stg, stt, starr, stgf, stft, stlen, stz, stx, free, stfree, stfw, cost, inv, wba, stwb, adx (accessors `Pre.<name>` below). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl : Nat) (s : State) : Prop :=
  (CallEnv R L s 4424 64) ∧
    (Serves R) ∧
    (s.mem.accessible thrA 8 false = true) ∧
    (s.mem.readLE thrA 8 = 12) ∧
    (Outside thrA 8 (win s 4424 64)) ∧
    (0 < xl) ∧
    (zl = 2 * xl) ∧
    (zl ≤ zc) ∧
    (zc < 2 ^ 40) ∧
    (NatLive s.mem R L zp zl) ∧
    (Outside zp (8 * zl) (win s 4424 64)) ∧
    (Apart zp (8 * zl) ((s.regs 14).toNat + 16) 8) ∧
    (Apart zp (8 * zl) (s.fsBase.toNat - 8) 8) ∧
    (s.mem.accessible xp (8 * xl) false = true) ∧
    (xp + 8 * xl ≤ 2 ^ 48) ∧
    (Held R L xp (8 * xl)) ∧
    (Outside xp (8 * xl) (win s 4424 64)) ∧
    (Apart zp (8 * zl) xp (8 * xl)) ∧
    (StkOK s.mem R L st) ∧
    (Outside st 24 (win s 4424 64)) ∧
    (Apart st 24 ((s.regs 14).toNat + 16) 8) ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4424 64) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    (Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    (Apart (freeP s.mem st) (freeN s.mem st) (s.fsBase.toNat - 8) 8) ∧
    (stLen s.mem st + 2 * xl + 3 ≤ 2 ^ 16) ∧
    (Apart st 24 zp (8 * zl)) ∧
    (Apart st 24 xp (8 * xl)) ∧
    (Apart zp (8 * zl) (freeP s.mem st) (freeN s.mem st) ∧ Apart xp (8 * xl) (freeP s.mem st) (freeN s.mem st)) ∧
    (Apart st 24 (freeP s.mem st) (freeN s.mem st)) ∧
    (Outside (freeP s.mem st) (freeN s.mem st) (win s 4424 64)) ∧
    (stackNatCost (stLen s.mem st) (2 * xl) ≤ b) ∧
    (R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) ∧
    (s.mem.accessible StackNat.wbA 4 false = true) ∧
    (Apart st 24 StackNat.wbA 4) ∧
    (s.mem.accessible Callees.adxAddr 1 false = true)

theorem Pre.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : CallEnv R L s 4424 64 := h.1
theorem Pre.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Serves R := h.2.1
theorem Pre.thA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : s.mem.accessible thrA 8 false = true := h.2.2.1
theorem Pre.thV {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : s.mem.readLE thrA 8 = 12 := h.2.2.2.1
theorem Pre.thO {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Outside thrA 8 (win s 4424 64) := h.2.2.2.2.1
theorem Pre.x0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : 0 < xl := h.2.2.2.2.2.1
theorem Pre.zl2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : zl = 2 * xl := h.2.2.2.2.2.2.1
theorem Pre.zlc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : zl ≤ zc := h.2.2.2.2.2.2.2.1
theorem Pre.zcb {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : zc < 2 ^ 40 := h.2.2.2.2.2.2.2.2.1
theorem Pre.zlive {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : NatLive s.mem R L zp zl := h.2.2.2.2.2.2.2.2.2.1
theorem Pre.zw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Outside zp (8 * zl) (win s 4424 64) := h.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart zp (8 * zl) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zt {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart zp (8 * zl) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.xacc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : s.mem.accessible xp (8 * xl) false = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.x48 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : xp + 8 * xl ≤ 2 ^ 48 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.xh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Held R L xp (8 * xl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.xw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Outside xp (8 * xl) (win s 4424 64) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.zx {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart zp (8 * zl) xp (8 * xl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stok {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : StkOK s.mem R L st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Outside st 24 (win s 4424 64) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stt {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.starr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4424 64) ∧ Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stgf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart (freeP s.mem st) (freeN s.mem st) ((s.regs 14).toNat + 16) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stft {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart (freeP s.mem st) (freeN s.mem st) (s.fsBase.toNat - 8) 8 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stlen {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : stLen s.mem st + 2 * xl + 3 ≤ 2 ^ 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stz {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 zp (8 * zl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stx {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 xp (8 * xl) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.free {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart zp (8 * zl) (freeP s.mem st) (freeN s.mem st) ∧ Apart xp (8 * xl) (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfree {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 (freeP s.mem st) (freeN s.mem st) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stfw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Outside (freeP s.mem st) (freeN s.mem st) (win s 4424 64) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : stackNatCost (stLen s.mem st) (2 * xl) ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.wba {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : s.mem.accessible StackNat.wbA 4 false = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.stwb {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : Apart st 24 StackNat.wbA 4 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.adx {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (h : Pre R b L st zp zl zc xp xl s) : s.mem.accessible Callees.adxAddr 1 false = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The writes a caller sees: `z[0:2n]`, the stack header and the free part of the stack array. -/
@[reducible] def ws (m : Memory) (st zp zl : Nat) : List (Nat × Nat) := (zp, zp + 8 * zl) :: stkWs m st

/-- The postcondition. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl xp xl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ natVal s'.mem zp zl = natVal s.mem xp xl * natVal s.mem xp xl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) (2 * xl) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4424 64 ++ ws s.mem st zp zl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem st zp zl)

/-- The register part of the postcondition (what `Ensures.toSummaryIn` keeps). -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

/-! ## The large path (`n ≥ 12`) after `t := stk.nat(2n)` -/

/-- the facts fixed from the `stk.nat` call on (see the arm64 twin), plus the entry's `X15`, `DF` and return address -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L st zp zl zc xp xl s
  big : 12 ≤ xl
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t (2 * xl)
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) (2 * xl) ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1
  amem : ¬(w1 = stW s.mem st ∧ c1 = stCap s.mem st) → (w1, w1 + 8 * c1) ∈ L1
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  ra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- the memory facts at every point after the `stk.nat` call (memory `M`, the stack's `len` `l1`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (l1 : Nat) (M : Memory) : Prop where
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  tl : M.readLE ((s.regs 4).toNat - 88) 8 = 2 * xl
  tc : M.readLE ((s.regs 4).toNat - 80) 8 = 2 * xl
  tp : M.readLE ((s.regs 4).toNat - 48) 8 = t
  dfn : M.readLE ((s.regs 4).toNat - 40) 8 = segAddr LibBasicSqr.program (fn ++ ".deferwrap1")
  dst : M.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : M.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s1 : M.readLE ((s.regs 4).toNat + 16) 8 = zp
  s2 : M.readLE ((s.regs 4).toNat + 24) 8 = zl
  s3 : M.readLE ((s.regs 4).toNat + 32) 8 = zc
  s4 : M.readLE ((s.regs 4).toNat + 40) 8 = xp
  s5 : M.readLE ((s.regs 4).toNat + 48) 8 = xl
  s6 : M.readLE ((s.regs 4).toNat + 56) 8 = xc
  hw : M.readLE st 8 = w1
  hl : M.readLE (st + 8) 8 = l1
  hc : M.readLE (st + 16) 8 = c1
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  xs : ∀ a n, xp ≤ a → a + n ≤ xp + 8 * xl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ win s 4424 64 ++ [(zp, zp + 8 * zl), (t, t + 16 * xl)] ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L ([(zp, zp + 8 * zl), (t, t + 16 * xl)] ++ stkWs s.mem st)
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M)

/-- the loop head (`CMPQ DI, AX`, `RAX = i`) -/
abbrev head : Nat := segAddr Extracted.program fn + 0x1c0

/-- what holds at the loop head in iteration `i` (memory `M`): the frame record, `z[0:2i] = Σ_{j<i} x_j² B^(2j)`,
`t[0:2i] = Σ_{j<i} x_j·x[0:j]·B^j`, the rest of `t` still zero. -/
def Inv (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (i : Nat) (M : Memory) : Prop :=
  Mem R L st zp zl zc xp xl xc s t L1 b1 w1 c1 (stLen s.mem st + (2 * xl + 3) / 4 * 4) M ∧
    natVal M zp (2 * i) = SqrMath.sqS (SqrMath.lim s.mem xp) i ∧
    natVal M t (2 * i) = SqrMath.sqT (SqrMath.lim s.mem xp) i ∧
    ∀ a n, t + 16 * i ≤ a → a + n ≤ t + 16 * xl → M.readLE a n = 0

end FvModexp.Amd64.BasicSqr
