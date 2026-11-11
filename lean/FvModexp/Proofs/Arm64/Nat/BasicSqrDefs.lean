import FvModexp.Proofs.Arm64.Nat.LibBasicSqr
import FvModexp.Proofs.Arm64.Nat.BasicMul
import FvModexp.Proofs.Arm64.Nat.Callees2
import FvModexp.Proofs.Arm64.Nat.Restore
import FvModexp.Proofs.Arm64.Exp.ExpHyp
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.SqrMath

/-!
# `basicSqr(stk, z, x nat)` (go-bigmodexpfix natmul.go:113), arm64 — statement and the relations between segments

```go
func basicSqr(stk *stack, z, x nat) {
	n := len(x)
	if n < basicSqrThreshold { basicMul(z, x, x); return }
	defer stk.restore(stk.save())
	t := stk.nat(2 * n)
	clear(t)
	z[1], z[0] = mulWW(x[0], x[0]) // the initial square
	for i := 1; i < n; i++ {
		d := x[i]
		z[2*i+1], z[2*i] = mulWW(d, d)
		t[2*i] = addMulVVWW(t[i:2*i], t[i:2*i], x[0:i], d, 0)
	}
	t[2*n-1] = lshVU(t[1:2*n-1], t[1:2*n-1], 1) // double the j < i products
	addVV(z, z, t)                              // combine the result
}
```
Args `X0 = stk`, `X1..X3 = z`, `X4..X6 = x`. Frame 208 (`MOVD.W R30, -208(RSP)`, `SP' = SP - 208`), spills `X1..X6` at
`SP + 16 … SP + 64` (`above = 64`); deepest callee `basicMul` (`stk 4224`): `stk = 208 + 4224 = 4432`.
Locals (offsets from `SP`): `t` at `-48` (ptr), `-88` (len), `-80` (cap); `2n` at `-56` (`2n - 1` after the loop);
the defer record `{deferwrap1, stk, len(stk.w)}` at `-40, -32, -24`, its address at `-16`, the defer bit at `-89`.
`(*stack).nat` is a premise in agent expmc's `ExpHyp.StackNatHyp` shape (top's planned summary).

The result: `z[0:2n] = x²`; the stack comes back with its `len` (`StackBack`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.BasicSqr

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr"
def names : List String := LibBasicSqr.names

/-- `basicSqrThreshold` (natmul.go:68, a writable global) -/
abbrev thrA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold»

/-- the free part of the stack array -/
@[reducible] def freeP (m : Memory) (st : Nat) : Nat := stW m st + 8 * stLen m st
@[reducible] def freeN (m : Memory) (st : Nat) : Nat := 8 * (stCap m st - stLen m st)

/-- The precondition (args `st`, `z = (zp, zl, zc)`, `x = (xp, xl, _)`). -/
structure Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl : Nat) (s : State) : Prop where
  ce : CallEnv R L s 4432 64
  sv : Serves R
  thA : s.mem.accessible thrA 8 false = true
  thV : s.mem.readLE thrA 8 = 12
  thO : Outside thrA 8 (win s 4432 64)
  x0 : 0 < xl
  zl2 : zl = 2 * xl
  zlc : zl ≤ zc
  zcb : zc < 2 ^ 40
  zlive : NatLive s.mem R L zp zl
  zw : Outside zp (8 * zl) (win s 4432 64)
  zg : Apart zp (8 * zl) ((s.regs 28).toNat + 16) 8
  xacc : s.mem.accessible xp (8 * xl) false = true
  x48 : xp + 8 * xl ≤ 2 ^ 48
  xh : Held R L xp (8 * xl)
  xw : Outside xp (8 * xl) (win s 4432 64)
  zx : Apart zp (8 * zl) xp (8 * xl)
  stok : StkOK s.mem R L st
  stw : Outside st 24 (win s 4432 64)
  stg : Apart st 24 ((s.regs 28).toNat + 16) 8
  starr : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 4432 64) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8
  stlen : stLen s.mem st + 2 * xl + 3 ≤ 2 ^ 16
  stz : Apart st 24 zp (8 * zl)
  stx : Apart st 24 xp (8 * xl)
  free : 0 < stCap s.mem st → Apart zp (8 * zl) (freeP s.mem st) (freeN s.mem st) ∧
    Apart xp (8 * xl) (freeP s.mem st) (freeN s.mem st)
  stfree : 0 < stCap s.mem st → Apart st 24 (freeP s.mem st) (freeN s.mem st)
  cost : ExpHyp.stackNatCost (stLen s.mem st) (2 * xl) ≤ b
  inv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- The writes a caller sees: `z[0:2n]`, the stack header and the free part of the stack array. -/
@[reducible] def ws (m : Memory) (st zp zl : Nat) : List (Nat × Nat) := (zp, zp + 8 * zl) :: stkWs m st

/-- The postcondition. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl xp xl : Nat) (s s' : State) : Prop :=
  natVal s'.mem zp zl = natVal s.mem xp xl * natVal s.mem xp xl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - ExpHyp.stackNatCost (stLen s.mem st) (2 * xl) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4432 64 ++ ws s.mem st zp zl) ∧
      LiveFrame s.mem s'.mem L (ws s.mem st zp zl)

/-! ## The large path (`n ≥ 12`) after `t := stk.nat(2n)` -/

/-- the facts fixed from the `stk.nat` call on: the scratch `t` (`2n` words), the live set `L1`, the budget `b1`, the
stack array `(w1, c1)` and the saved `len` `n0`. -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L st zp zl zc xp xl s
  big : 12 ≤ xl
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t (2 * xl)
  ext : LiveExt R L L1
  bud : b - ExpHyp.stackNatCost (stLen s.mem st) (2 * xl) ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1

/-- the memory facts at every point after the `stk.nat` call (memory `M`, the stack's `len` `l1`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (k : Nat) (l1 : Nat) (M : Memory) : Prop where
  lr : M.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat
  tl : M.readLE (s.sp.toNat - 88) 8 = 2 * xl
  tc : M.readLE (s.sp.toNat - 80) 8 = 2 * xl
  kk : M.readLE (s.sp.toNat - 56) 8 = k
  tp : M.readLE (s.sp.toNat - 48) 8 = t
  dfn : M.readLE (s.sp.toNat - 40) 8 = segAddr LibBasicSqr.program (fn ++ ".deferwrap1")
  dst : M.readLE (s.sp.toNat - 32) 8 = st
  dn : M.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : M.readLE (s.sp.toNat + 16) 8 = zp
  s2 : M.readLE (s.sp.toNat + 24) 8 = zl
  s3 : M.readLE (s.sp.toNat + 32) 8 = zc
  s4 : M.readLE (s.sp.toNat + 40) 8 = xp
  s5 : M.readLE (s.sp.toNat + 48) 8 = xl
  s6 : M.readLE (s.sp.toNat + 56) 8 = xc
  hw : M.readLE st 8 = w1
  hl : M.readLE (st + 8) 8 = l1
  hc : M.readLE (st + 16) 8 = c1
  xs : ∀ a n, xp ≤ a → a + n ≤ xp + 8 * xl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ winA s 4432 64 ++ [(zp, zp + 8 * zl), (t, t + 16 * xl)] ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L ([(zp, zp + 8 * zl), (t, t + 16 * xl)] ++ stkWs s.mem st)
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M)

/-- the loop head (`CMP R6, R3`, `R6 = i`) -/
abbrev head : Nat := segAddr Extracted.program fn + 0x140

/-- what holds at the loop head in iteration `i` (memory `M`): the frame record, `z[0:2i] = Σ_{j<i} x_j² B^(2j)`,
`t[0:2i] = Σ_{j<i} x_j·x[0:j]·B^j`, the rest of `t` still zero. -/
def Inv (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (i : Nat) (M : Memory) : Prop :=
  Mem R L st zp zl zc xp xl xc s t L1 b1 w1 c1 (2 * xl) (stLen s.mem st + (2 * xl + 3) / 4 * 4) M ∧
    natVal M zp (2 * i) = SqrMath.sqS (SqrMath.lim s.mem xp) i ∧
    natVal M t (2 * i) = SqrMath.sqT (SqrMath.lim s.mem xp) i ∧
    ∀ a n, t + 16 * i ≤ a → a + n ≤ t + 16 * xl → M.readLE a n = 0

end FvModexp.Arm64.BasicSqr
