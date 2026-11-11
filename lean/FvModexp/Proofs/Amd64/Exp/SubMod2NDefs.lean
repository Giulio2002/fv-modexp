import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Amd64.Exp.CallW
import FvModexp.Proofs.Amd64.Exp.CmpW
import FvModexp.Proofs.Amd64.Nat.NatSub
import FvModexp.Proofs.Amd64.Nat.NatAdd
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `nat.subMod2N` (go-bigmodexpfix nat.go:1726), amd64 — statement pieces (agent infra; twin of
`FvModexp.Arm64.SubMod2N`, same specialisation: `x = z`, `y` apart from `z`, `cap z ≥ ⌈n/64⌉`)

ABIInternal: `z = (RAX, RBX, RCX)`, `x = (RDI, RSI, R8)`, `y = (R9, R10, R11)`; the tenth argument `n` is on the stack at
`[RSP + 8]` (the precondition names it). Frame: `PUSHQ BP; SUBQ $0x78, SP` (`SP' = RSP - 128`); spills `[RSP + 16,
RSP + 88)` (`above = 88`, with the return-address slot and `n`); locals `[RSP - 56, RSP - 8)`, saved `BP` at
`[RSP - 8, RSP)`. Callees run with `RSP_c = RSP - 136`; the deepest is `nat.add` (`stk 4440`, `above 80`) →
`stk = 136 + 4440 = 4576`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.subMod2N"

theorem fnBase : segAddr LibExp.program fn = 6215840 := by decide

/-- stack bytes below `RSP` -/
abbrev K : Nat := 4576
/-- bytes above `RSP` (return address, `n`, the 9 register-argument spill words) -/
abbrev A : Nat := 88

/-- `⌈n / 64⌉` -/
@[reducible] def W (n : Nat) : Nat := (n + 63) / 64

/-- a `nat.make`-style request of at most `W n + 1` words, which bounds every allocation of `subMod2N` -/
@[reducible] def wCost (n : Nat) : Nat := allocCost (8 * (W n + 5))

/-- the budget: `trunc` of `y` into a fresh nat, `sub`, `trunc`, `add` (each at most `W n + 1` words) -/
@[reducible] def cost (n : Nat) : Nat := 5 * wCost n

/-- the entry facts specific to amd64: `z` apart from the TLS slot, the caller's return address a user address, `n` at
`[RSP + 8]`, the ABIInternal invariants `X15 = 0`, `DF = 0` -/
@[reducible] def Ent (s : State) (zp zc n : Nat) : Prop :=
  Apart zp (8 * zc) (s.fsBase.toNat - 8) 8 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.mem.readLE ((s.regs 4).toNat + 8) 8 = n ∧ s.xmm 15 = 0 ∧ s.df = false

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) : Prop :=
  CallEnv R L s K A ∧ Serves R ∧ Outside NatAdd.wordT 16 R.rt ∧ NatOne R L s.mem op (win s K A) ∧
    Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ W n ≤ zc ∧ zc < 2 ^ 40 ∧ zl ≤ 2 ^ 12 ∧ yl ≤ yc ∧ yc < 2 ^ 40 ∧ yl ≤ 2 ^ 12 ∧
    NatLive s.mem R L zp zc ∧ Outside zp (8 * zc) (win s K A) ∧ Apart zp (8 * zc) ((s.regs 14).toNat + 16) 8 ∧
    NatNorm s.mem zp zl ∧
    s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧ Held R L yp (8 * yl) ∧
    Outside yp (8 * yl) (win s K A) ∧ NatNorm s.mem yp yl ∧ Apart zp (8 * zc) yp (8 * yc) ∧
    cost n ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ Ent s zp zc n

@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = l' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n ∧
    NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - cost n ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s K A ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

end FvModexp.Amd64.SubMod2N
