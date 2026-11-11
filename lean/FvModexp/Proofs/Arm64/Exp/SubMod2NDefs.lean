import FvModexp.Proofs.Arm64.Exp.EvenHyp
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Arm64.Exp.CmpW
import FvModexp.Proofs.Arm64.Nat.NatSub
import FvModexp.Proofs.Arm64.Nat.NatAdd
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `nat.subMod2N` (go-bigmodexpfix nat.go:1726), arm64 — statement pieces (agent infra)

```go
func (z nat) subMod2N(x, y nat, n uint) nat {
	if uint(x.bitLen()) > n { if alias(z, x) { x = x.trunc(x, n) } else { x = nat(nil).trunc(x, n) } }
	if uint(y.bitLen()) > n { if alias(z, y) { y = y.trunc(y, n) } else { y = nat(nil).trunc(y, n) } }
	if x.cmp(y) >= 0 { return z.sub(x, y) }
	z = z.sub(y, x)
	for uint(len(z))*_W < n { z = append(z, 0) }
	for i := range z { z[i] = ^z[i] }
	z = z.trunc(z, n)
	return z.add(z, natOne)
}
```
Specialised to the two call sites in the reached code (`modularInverseModPowerOfTwo` nat.go:1324/1331 `z.subMod2N(z, zz, ·)`,
`expNNEven` nat.go:839 `z1.subMod2N(z1, z2, n)`): `x = z` (same slice), `y`'s array apart from `z`'s (so `alias(z, y)` is
false), `cap z ≥ ⌈n/64⌉` (both callers: `z` was made with at least that many words; so `append` never calls
`growslice`).

Frame 144 (`MOVD.W R30, -144(RSP)`); spills at `SP + 8 … SP + 80` (`above = 88`); locals `SP - 56 … SP - 16`.
Deepest callee: `nat.add` (`stk 4464`) → `stk = 144 + 4464 = 4608`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.subMod2N"

theorem fnBase : segAddr LibExp.program fn = 1805584 := by decide

/-- stack bytes below `SP` -/
abbrev K : Nat := 4608
/-- bytes above `SP` (the 10 argument spill words + saved LR slot of the caller's frame) -/
abbrev A : Nat := 88

/-- `⌈n / 64⌉` -/
@[reducible] def W (n : Nat) : Nat := (n + 63) / 64

/-- a `nat.make`-style request of at most `W n + 1` words, which bounds every allocation of `subMod2N` -/
@[reducible] def wCost (n : Nat) : Nat := allocCost (8 * (W n + 5))

/-- the budget: `trunc` of `y` into a fresh nat, `sub`, `trunc`, `add` (each at most `W n + 1` words); `trunc` of `x`
reuses `z` -/
@[reducible] def cost (n : Nat) : Nat := 5 * wCost n

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) : Prop :=
  CallEnv R L s K A ∧ Serves R ∧ Outside NatAdd.wordT 16 R.rt ∧ NatOne R L s.mem op (win s K A) ∧
    Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ W n ≤ zc ∧ zc < 2 ^ 40 ∧ zl ≤ 2 ^ 12 ∧ yl ≤ yc ∧ yc < 2 ^ 40 ∧ yl ≤ 2 ^ 12 ∧
    NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s K A) ∧ Apart zp (8 * zc) ((s.regs 28).toNat + 16) 8 ∧
    NatNorm s.mem zp zl ∧
    s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧ Held R L yp (8 * yl) ∧
    Outside yp (8 * yl) (win s K A) ∧ NatNorm s.mem yp yl ∧ Apart zp (8 * zc) yp (8 * yc) ∧
    cost n ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48

@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s s' : State) : Prop :=
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = l' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n ∧
    NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - cost n ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s K A ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

end FvModexp.Arm64.SubMod2N
