import FvModexp.Proofs.Arm64.Nat.LibNatAdd
import FvModexp.Proofs.Arm64.Nat.AsmCallees

/-!
# `nat.add` (go-bigmodexpfix nat.go:98), arm64: statement pieces (WIP — proof not started, see WIP-SORRY.txt)

```go
func (z nat) add(x, y nat) nat {
	m, n := len(x), len(y)
	switch {
	case m < n:  return z.add(y, x)          // the one self-call (then m ≥ n)
	case m == 0: return z[:0]
	case n == 0: return z.set(x)             // make(m) + copy
	}
	z = z.make(m + 1)
	c := addVV(z[:n], x[:n], y[:n])
	if m > n { c = addVW(z[n:m], x[n:], c) }
	z[m] = c
	return z.norm()
}
```
Frame 160 (`MOVD.W R30, -160(RSP)`), spills `X0, X3, X4, X5, X6, X7, X8` at `SP + 8 … SP + 72` (`above = 80`).
Deepest callee in the body (`len y ≤ len x`): `addVW` (`stk 4144`) → body `stk = 160 + 4144 = 4304`; the self-call adds one
frame: `stk = 160 + 4304 = 4464`. Plan: `body` = a `Summary` at the entry for `len y ≤ len x` (no `RetAddr` issue at the
self-call), `ens` = run until the self-call + `body`, or `Summary.returns body`.

Aliasing of the real call sites (`(*Int).Add/Sub` → `z.abs.add(x.abs, y.abs)` with `z = x` possible): `z = x ∨ Apart`,
`z = y ∨ Apart`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatAdd

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.add"
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `max(len x, len y)`, the length of the longer operand. -/
@[reducible] def mx (xl yl : BitVec 64) : Nat := max xl.toNat yl.toNat

/-- The capacity `nat.add` needs: `m + 1` (`make(m + 1)`), or `m` for `z.set(x)` when the shorter operand is empty. -/
@[reducible] def need (xl yl : BitVec 64) : Nat := if min xl.toNat yl.toNat = 0 then mx xl yl else mx xl yl + 1

/-- The precondition (requests: one `makeslice` when `z` is too small, the `memmove` of `z.set(x)` and the `addVW`
copies, to any runtime-chosen destination). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4464 80 ∧ Outside wordT 16 R.rt ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4464 80) ∧
      Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4464 80) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4464 80) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl yl → R.ok (cA "runtime.makeslice") [wordT, need xl yl, makeCap (need xl yl)] ∧
      makeCost (need xl yl) ≤ b) ∧
    (∀ d src k, k ≤ 8 * mx xl yl → R.ok (cA "runtime.memmove") [d, src, k])

/-- The postcondition: a normalised nat `(p', n', c')` holding `X + Y`, `z`'s array or a fresh one. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s s' : State) :
    Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ mx xl yl + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl yl) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4464 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

end FvModexp.Arm64.NatAdd
