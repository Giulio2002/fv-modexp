import FvModexp.Proofs.Arm64.Nat.LibDivL
import FvModexp.Proofs.Arm64.Nat.DrsIface

set_option autoImplicit false

/-!
# `(z nat) divLarge(stk *stack, u, uIn, vIn nat) (q, r nat)` (go-bigmodexpfix natdiv.go:597), arm64 — statements

```go
func (z nat) divLarge(stk *stack, u, uIn, vIn nat) (q, r nat) {
	n := len(vIn); m := len(uIn) - n
	defer stk.restore(stk.save())
	shift := nlz(vIn[n-1])
	v := stk.nat(n)
	u = u.make(len(uIn) + 1)
	if shift == 0 { copy(v, vIn); copy(u[:len(uIn)], uIn); u[len(uIn)] = 0
	} else { lshVU(v, vIn, shift); u[len(uIn)] = lshVU(u[:len(uIn)], uIn, shift) }
	if alias(z, u) { z = nil }
	q = z.make(m + 1)
	if n < divRecursiveThreshold { q.divBasic(stk, u, v) } else { q.divRecursive(stk, u, v) }
	q = q.norm()
	if shift != 0 { rshVU(u, u, shift) }
	r = u.norm()
	return q, r
}
```
Arguments `X0..X2 = z`, `X3 = stk`, `X4..X6 = u` (the remainder's storage), `X7..X9 = uIn`, `X10..X12 = vIn`; results
`X0..X2 = q`, `X3..X5 = r`. Frame 304 (`SUB $304, RSP, R20; STP (R29, R30), -8(R20)`): saved `X30` at `SP - 304`, `X29` at
`SP - 312`; spills `SP + 8 … SP + 104` (`above = 112`). The window `41264 = 304 + 40960` covers the deepest callee
`divRecursiveStep` (window `40960`, see `DrsPre`).

`divRecursiveStep` (natdiv.go:750) is a premise here (`DrsHyp`, its own proof composes it); the statement of `divLarge`
is the internal summary that `nat.div` / `nat.rem` compose. `u` may be `uIn` itself (same pointer: `Int.QuoRem` with
`r = x`); then the copy is skipped and the shift is done in place.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.DivLarge

def names : List String := LibDivL.names

/-- the budget of `divLarge`: `stk.nat(n)`, `u.make(len uIn + 1)`, `z.make(m + 1)` and the division
(`divBasic`: `stk.nat(n + 1)`; `divRecursiveStep`: `dc`) -/
@[reducible] def cost (dc : Nat → Nat → Nat → Nat) (l il vl : Nat) : Nat :=
  stackNatCost l vl + makeCost (il + 1) + makeCost (il - vl + 1) +
    max (stackNatCost (l + StackNat.rnd vl) (vl + 1)) (dc (l + StackNat.rnd vl) (il + 1) vl)

/-- The precondition (args `z = (zp, _, zc)`, `st`, `u = (up, _, uc)`, `uIn = (ip, il, _)`, `vIn = (vp, vl, _)`). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State) :
    Prop :=
  CallEnv R L s 41264 112 ∧ Serves R ∧ RunIface.Globals R s.mem (win s 41264 112) ∧
  ExpHyp.WrOut R L s 41264 112 zp zc ∧ ExpHyp.WrOut R L s 41264 112 up uc ∧
  ExpHyp.RdIn R L s 41264 112 ip il ∧ ExpHyp.RdIn R L s 41264 112 vp vl ∧
  2 ≤ vl ∧ vl ≤ il ∧ il ≤ 2 ^ 9 ∧ NatNorm s.mem vp vl ∧
  (0 < zc → 0 < uc → Apart zp (8 * zc) up (8 * uc)) ∧
  (0 < zc → Apart zp (8 * zc) ip (8 * il) ∧ Apart zp (8 * zc) vp (8 * vl)) ∧
  (0 < uc → Apart up (8 * uc) vp (8 * vl)) ∧
  (up = ip ∨ (0 < uc → Apart up (8 * uc) ip (8 * il))) ∧
  EvenHyp.StkIn R L s 41264 112 st ∧ stLen s.mem st + 16 * il + 64 ≤ 2 ^ 16 ∧
  (0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (0 < uc → Apart up (8 * uc) st 24 ∧ Apart up (8 * uc) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart ip (8 * il) st 24 ∧ Apart ip (8 * il) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
  (Apart vp (8 * vl) st 24 ∧ Apart vp (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
  ((stCap s.mem st = 0 → stW s.mem st = 0) ∧ st ≠ 0) ∧
  ((0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < uc → Apart up (8 * uc) RunIface.gA 32) ∧
    Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32) ∧
  c ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem Pre.ce {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : CallEnv R L s 41264 112 := h.1
theorem Pre.sv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Serves R := h.2.1
theorem Pre.gl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : RunIface.Globals R s.mem (win s 41264 112) := h.2.2.1
theorem Pre.zo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : ExpHyp.WrOut R L s 41264 112 zp zc := h.2.2.2.1
theorem Pre.uo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : ExpHyp.WrOut R L s 41264 112 up uc := h.2.2.2.2.1
theorem Pre.io {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : ExpHyp.RdIn R L s 41264 112 ip il := h.2.2.2.2.2.1
theorem Pre.vo {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : ExpHyp.RdIn R L s 41264 112 vp vl := h.2.2.2.2.2.2.1
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
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : EvenHyp.StkIn R L s 41264 112 st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : stCap s.mem st = 0 → stW s.mem st = 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
theorem Pre.st0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : st ≠ 0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
theorem Pre.fw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : Outside (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (win s 41264 112) := by
  have h0 := h.w0
  have h1 := h.sti.1.2.2.2.2.2.1
  have h2 := h.ce.2.1
  by_cases hc : 0 < stCap s.mem st
  · have := (h.sti.2.2.2 hc).1
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  · have := h0 (by omega)
    simp only [win, outside_cons, outside_nil, and_true]; rw [this]; omega
theorem Pre.ga {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧
      (0 < uc → Apart up (8 * uc) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : c ≤ b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Pre.inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (h : Pre R b L c zp zc st up uc ip il vp vl s) : R.inv b L (s.regs 28).toNat (view R.rt L s.mem) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


/-- an array's range, empty when `c = 0` (the pointer of a `cap = 0` nat is arbitrary) -/
@[reducible] def ar (p c : Nat) : List (Nat × Nat) := if 0 < c then [(p, p + 8 * c)] else []

/-- The postcondition: `q = U / V` (old `z` array or a fresh one), `r = U mod V` (old `u` array or a fresh one; a fresh
one is apart from the stack's final array), both normalised; the stack's `len` restored. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem ip il / natVal s.mem vp vl) ∧
      ExpHyp.NatOF R L L' s'.mem up uc 1 r rl rc (natVal s.mem ip il % natVal s.mem vp vl) ∧
      ExpHyp.RtPost R b c L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = up ∧ rc = uc) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 41264 112 ++ (ar zp zc ++ ar up uc) ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ((ar zp zc ++ ar up uc) ++ stkWs s.mem st)

/-- `divLarge`'s `Ensures` with budget bound `cost dc` -/
def Hyp (impl : List Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc ip il ic vp vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, u, ul, uc, ip, il, ic, vp, vl, vc]
      (fun s => Pre R b L (cost dc (stLen s.mem st.toNat) il.toNat vl.toNat) z.toNat zc.toNat st.toNat u.toNat uc.toNat
        ip.toNat il.toNat vp.toNat vl.toNat s)
      (fun s s' => Post R b L (cost dc (stLen s.mem st.toNat) il.toNat vl.toNat) z.toNat zc.toNat st.toNat u.toNat
        uc.toNat ip.toNat il.toNat vp.toNat vl.toNat s s')

end FvModexp.Arm64.DivLarge
