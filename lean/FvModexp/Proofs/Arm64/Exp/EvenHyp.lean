import FvModexp.Proofs.Arm64.Exp.ExpHyp

/-!
# Callee premises of the power-of-two / even branch of the exp layer (arm64; agent infra) — hypotheses until the owners land

`nat.trunc` (owner asm, not started) as an `Ensures` premise in the CONVENTIONS §3 / `ExpHyp` shape, parametric in the
owner's `ns`, `stk`, `above`; and the writable global `natOne` (`var natOne = nat{1}`, nat.go:30) that `subMod2N` reads.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes RtPost)

/-! ## `z.trunc(x, n)` (nat.go:530) — z X0..X2, x X3..X5, n X6; result `x mod 2^n` normalised

Go: `w := (n + 63) / 64; if len(x) < w { return z.set(x) }; z = z.make(w); copy(z, x); mask the top word; z.norm()`,
so the capacity it needs is `min (len x) w` (`z.make`), and it copies with `memmove`. `z = x` is allowed. A fresh
array (`cap z < need`) has capacity at least `need` (`nat.make`). -/

def fnTrunc : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc"

/-- the capacity `z.trunc(x, n)` needs -/
@[reducible] def truncNeed (xl n : Nat) : Nat := min xl ((n + 63) / 64)

@[reducible] def TruncPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl n : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (truncNeed xl n) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def TruncPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl n : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (truncNeed xl n) p' l' c' (natVal s.mem x xl % 2 ^ n) ∧
      (zc < truncNeed xl n → truncNeed xl n ≤ c') ∧
      RtPost R b (makeCost (truncNeed xl n)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

def TruncHyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnTrunc)
      [z, zl, zc, x, xl, xc, n]
      (fun s => TruncPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s)
      (fun s s' => TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

/-! ## The global `natOne` (nat.go:30, `.data`): header `(op, 1, 1)`, `op[0] = 1` -/

@[reducible] def natOneA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne»

/-- `natOne` as `subMod2N`'s final `z.add(z, natOne)` reads it: header at `natOneA` and word at `op` readable, held,
outside the runtime ranges and outside the stack ranges `w`. -/
@[reducible] def NatOne (R : RtInv) (L : List (Nat × Nat)) (m : Memory) (op : Nat) (w : List (Nat × Nat)) : Prop :=
  m.readLE natOneA 8 = op ∧ m.readLE (natOneA + 8) 8 = 1 ∧ m.readLE (natOneA + 16) 8 = 1 ∧ m.readLE op 8 = 1 ∧
    m.accessible natOneA 24 false = true ∧ Outside natOneA 24 R.rt ∧ Outside natOneA 24 w ∧
    m.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L op 8 ∧ Outside op 8 w

end FvModexp.Arm64.EvenHyp
