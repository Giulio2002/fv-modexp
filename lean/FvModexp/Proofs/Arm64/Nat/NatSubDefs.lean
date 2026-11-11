import FvModexp.Proofs.Arm64.Nat.LibNatSub
import FvModexp.Proofs.Arm64.Nat.AsmCallees

/-!
# `nat.sub` (go-bigmodexpfix nat.go:120), arm64: statement pieces

```go
func (z nat) sub(x, y nat) nat {
	m, n := len(x), len(y)
	switch {
	case m < n:  panic("underflow")
	case m == 0: return z[:0]
	case n == 0: return z.set(x)
	}
	z = z.make(m)
	c := subVV(z[0:n], x, y)
	if m > n { c = subVW(z[n:], x[n:], c) }
	if c != 0 { panic("underflow") }
	return z.norm()
}
```
The precondition excludes both panics: `len y ≤ len x` and `Y ≤ X`. Frame 160, spills at `SP + 8 … SP + 80`;
deepest callee `subVW` (`stk 4144`): `stk = 4304` (no self-call).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatSub

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sub"
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- The precondition (requests: one `makeslice` when `z` is too small, the `memmove` of `z.set(x)` and the `addVW`
copies, to any runtime-chosen destination). -/
def PreS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s stk 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧ Outside xp.toNat (8 * xl.toNat) (win s stk 80) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s stk 80) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

@[reducible] def Pre := PreS 4304

/-- The postcondition: a normalised nat `(p', n', c')` holding `X + Y`, `z`'s array or a fresh one. -/
@[reducible] def PostS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s s' : State) :
    Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost xl.toNat ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

@[reducible] def Post := PostS 4304

/-- `PostS` with the facts a caller making a second call needs (infra s5 request): `z` reused when its capacity
suffices, the result capacity bounded. -/
@[reducible] def PostR (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64)
    (s s' : State) : Prop :=
  PostS stk R b L zp zc xp xl yp yl s s' ∧
    (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
    (xl.toNat < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40)

end FvModexp.Arm64.NatSub
