import FvModexp.Proofs.Amd64.Exp.LibExp
import FvModexp.Proofs.Amd64.Top.RunIface

/-!
# Callee premises of the power-of-two / even branch of the exp layer (amd64; agent infra) — twin of
`FvModexp.Arm64.EvenHyp`

The CONVENTIONS §3 shape pieces `RdIn`/`WrOut`/`NatRes`/`RtPost` (amd64 twins of `Arm64.ExpHyp`'s; `g = R14`,
window `win`), `nat.trunc` (owner asm, not landed) as an `Ensures` premise, and the writable global `natOne`.
amd64 posts start with `s'.fsBase = s.fsBase`; the premise also states `s'.df = s.df` (every later callee call needs
`DF = 0`, which `ABIReturn` does not carry).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.EvenHyp

open FvModexp.Amd64.RunIface (Serves)

/-- a read-only input array `p[0:n]` of a callee whose window is `win s stk above` -/
@[reducible] def RdIn (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above p n : Nat) : Prop :=
  n < 2 ^ 40 ∧ s.mem.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ Held R L p (8 * n) ∧
    Outside p (8 * n) (win s stk above)

/-- a reused output array `p[0:c]` -/
@[reducible] def WrOut (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive s.mem R L p c ∧ (0 < c → Outside p (8 * c) (win s stk above) ∧
    Apart p (8 * c) ((s.regs 14).toNat + 16) 8 ∧ Apart p (8 * c) (s.fsBase.toNat - 8) 8)

/-- the result nat `(p', l', c')` of a function that reuses `z = (zp, zc)` when `zc ≥ need` and allocates otherwise -/
@[reducible] def NatRes (R : RtInv) (L L' : List (Nat × Nat)) (m' : Memory) (zp zc need p' l' c' v : Nat) : Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    (need ≤ zc → p' = zp ∧ c' = zc) ∧
    (zc < need → 0 < c' → InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)

/-- the runtime-side post of every shape: live set grown, budget, invariant -/
@[reducible] def RtPost (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat)) (b' : Nat) (s s' : State) : Prop :=
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem)

/-! ## `z.trunc(x, n)` (nat.go:530) — z RAX,RBX,RCX, x RDI,RSI,R8, n R9; result `x mod 2^n` normalised -/

def fnTrunc : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc"

/-- the capacity `z.trunc(x, n)` needs -/
@[reducible] def truncNeed (xl n : Nat) : Nat := min xl ((n + 63) / 64)

@[reducible] def TruncPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl n : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (truncNeed xl n) ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

@[reducible] def TruncPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl n : Nat) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 3 = BitVec.ofNat 64 l' ∧ s'.regs 1 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (truncNeed xl n) p' l' c' (natVal s.mem x xl % 2 ^ n) ∧
      (zc < truncNeed xl n → truncNeed xl n ≤ c') ∧
      RtPost R b (makeCost (truncNeed xl n)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

def TruncHyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnTrunc)
      [z, zl, zc, x, xl, xc, n]
      (fun s => TruncPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s)
      (fun s s' => TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

/-! ## The global `natOne` (nat.go:30, `.data`): header `(op, 1, 1)`, `op[0] = 1` -/

@[reducible] def natOneA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne»

/-- `natOne` as `subMod2N`'s final `z.add(z, natOne)` reads it -/
@[reducible] def NatOne (R : RtInv) (L : List (Nat × Nat)) (m : Memory) (op : Nat) (w : List (Nat × Nat)) : Prop :=
  m.readLE natOneA 8 = op ∧ m.readLE (natOneA + 8) 8 = 1 ∧ m.readLE (natOneA + 16) 8 = 1 ∧ m.readLE op 8 = 1 ∧
    m.accessible natOneA 24 false = true ∧ Outside natOneA 24 R.rt ∧ Outside natOneA 24 w ∧
    m.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L op 8 ∧ Outside op 8 w

end FvModexp.Amd64.EvenHyp
