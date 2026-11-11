import FvModexp.Proofs.Amd64.Exp.LibMont

/-!
# `nat.montgomery` (amd64): callee shapes (HYPOTHESES until agent asm's summaries land)

The ABI0 kernels `addMulVVWW` and `subVV` are owned by agent asm. Until their summaries exist, the montgomery proof takes
them as premises of exactly these shapes (`Summary0` on the montgomery library program); the real summaries are moved in
with `Summary.of_codeIn` and, if their statements differ, a `Summary.mono` bridge. Listed in docs/COVERAGE (hypothesis).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.MontHyp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"
def subFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0"
def amvFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"
/-- the loop head (`CMPQ BX, R11`), nat.go:199 -/
abbrev head : Nat := segAddr LibMont.program fn + 0x202
/-- `math/big.hasADX` (read by addMulVVWW) -/
abbrev hasADX : Nat := 0xbb6b8a

/-- assumed shape of the `addMulVVWW.abi0` summary (frame words z,zl,zc,x,xl,xc,y,yl,yc,m,a at sp+8..; result c at sp+96):
`z = (x + y*m + a) mod 2^(64n)`, `c = (x + y*m + a) / 2^(64n)` (values before the call). -/
abbrev AmvPre (s : State) : Prop :=
  (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 104 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat) 104 true = true ∧ s.mem.accessible hasADX 1 false = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) true = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = s.mem.readLE ((s.regs 4).toNat + 32) 8 ∨
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ((s.regs 4).toNat + 96) 8

abbrev amvVal (s : State) : Nat :=
  s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) +
  s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) *
    s.mem.readLE ((s.regs 4).toNat + 80) 8 + s.mem.readLE ((s.regs 4).toNat + 88) 8

abbrev AmvQ (s : State) (m : Memory) : Prop :=
  m.readLE (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      amvVal s % 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 96) 8 = amvVal s / 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8), ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]

/-- assumed shape of the `subVV.abi0` summary (frame words z,zl,zc,x,xl,xc,y,yl,yc at sp+8.., result at sp+80) -/
abbrev SubPre (s : State) : Prop :=
  (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 88 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat) 88 true = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) true = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ((s.regs 4).toNat + 80) 8

abbrev SubQ (s : State) (m : Memory) : Prop :=
  m.readLE (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      (s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) +
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) -
        s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)) %
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

end FvModexp.Amd64.MontHyp
