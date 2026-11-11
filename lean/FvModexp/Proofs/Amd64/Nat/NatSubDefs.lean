import FvModexp.Proofs.Amd64.Nat.LibNatSub
import FvModexp.Proofs.Amd64.Nat.AsmCallees

/-!
# `nat.sub` (go-bigmodexpfix nat.go:120), amd64: statement pieces (see the arm64 twin `FvModexp.Arm64.NatSub`)

Frame as `nat.add` (amd64); `stk = 4288` (no self-call). Arguments `z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `y = (R9, R10, R11)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatSub

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sub"
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

def PreS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s stk 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧ Outside xp.toNat (8 * xl.toNat) (win s stk 80) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s stk 80) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

@[reducible] def Pre := PreS 4288

@[reducible] def PostS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost xl.toNat ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

@[reducible] def Post := PostS 4288

end FvModexp.Amd64.NatSub
