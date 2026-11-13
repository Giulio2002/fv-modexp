import FvModexp.Proofs.Amd64.NatQ.DivHypQ
import FvModexp.Proofs.Amd64.Nat.LibRem
import FvModexp.Proofs.Amd64.Nat.LibDiv

set_option autoImplicit false

/-!
# `z.rem(stk, u, v)` (amd64, Q-form) — definitions (twin of Arm64/NatQ/RemDefs.lean; TIGHT COSTS, asm s40)

go-bigmodexpfix natdiv.go:505-513:
```go
func (z nat) rem(stk *stack, u, v nat) (r nat) {
	if alias(z, u) {
		z = nil
	}
	defer stk.restore(stk.save())
	q := stk.nat(max(1, len(u)-(len(v)-1)))
	_, r = q.div(stk, z, u, v)
	return r
}
```
amd64 ABIInternal: `z` RAX,RBX,RCX, `stk` RDI, `u` RSI,R8,R9, `v` on the stack at `RSP+8 … RSP+24` (entry `RSP = r`);
result `RAX,RBX,RCX`. Frame: `PUSHQ BP` (`[r-8]`), `SUBQ $0xc0, SP` (`RSP = r - 200`); spills `z.ptr` `r+32`, `stk` `r+56`,
`u` `r+64, r+72, r+80`; defer bit `r-89`; result slots `r-72 … r-56`; `z` (after the alias test) `r-48` ptr, `r-88` len,
`r-80` cap; the closure `{deferwrap1, stk, len}` at `r-40 … r-24`, its pointer at `r-16`. Both callees run at
`RSP = r - 208`: `(*stack).nat` (window `4192 / 24`) and `nat.div` (window `41512 / 112`, its stack args `u`, `v` at
`r-200 … r-160`), so `rem`'s window is `41720 / 112`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem"

/-- the segment base of `nat.rem` -/
abbrev base : Nat := 0x5edca0

/-- the deferred closure's code `nat.rem.deferwrap1` -/
abbrev dfnA : Nat := 0x5edee0

/-- `CALL (*stack).nat` -/
abbrev callNat : Nat := 0x5edd99

/-- `CALL nat.div` -/
abbrev callDiv : Nat := 0x5ede05

/-- `CALL CX` (the deferred closure) -/
abbrev callDfr : Nat := 0x5ede32

/-- the scratch length `max(1, len u - (len v - 1))` -/
@[reducible] def kq (ul vl : Nat) : Nat := ul - vl + 1

/-- the stack need: `stk.nat(k)` then `div` at length `len + rnd k` (`+ 16·len u + 64`) -/
@[reducible] def need (ul _vl : Nat) : Nat := 17 * ul + 68

/-- the ranges `rem` writes in its own frame -/
@[reducible] def fw (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 208, (s.regs 4).toNat), ((s.regs 4).toNat + 32, (s.regs 4).toNat + 88)]

/-- the frame slots read after `stk.nat` (memory `M`; `r` = the entry `RSP`) -/
structure Sl (s : State) (zp zl zc st up ul uc : Nat) (M : Memory) : Prop where
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : M.readLE ((s.regs 4).toNat - 89) 1 = 1
  zp' : M.readLE ((s.regs 4).toNat - 48) 8 = zp
  zl' : M.readLE ((s.regs 4).toNat - 88) 8 = zl
  zc' : M.readLE ((s.regs 4).toNat - 80) 8 = zc
  dfn : M.readLE ((s.regs 4).toNat - 40) 8 = dfnA
  dst : M.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : M.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s1 : M.readLE ((s.regs 4).toNat + 56) 8 = st
  s2 : M.readLE ((s.regs 4).toNat + 64) 8 = up
  s3 : M.readLE ((s.regs 4).toNat + 72) 8 = ul
  s4 : M.readLE ((s.regs 4).toNat + 80) 8 = uc
  v1 : M.readLE ((s.regs 4).toNat + 8) 8 = s.mem.readLE ((s.regs 4).toNat + 8) 8
  v2 : M.readLE ((s.regs 4).toNat + 16) 8 = s.mem.readLE ((s.regs 4).toNat + 16) 8
  v3 : M.readLE ((s.regs 4).toNat + 24) 8 = s.mem.readLE ((s.regs 4).toNat + 24) 8

/-- the facts at `CALL (*stack).nat` (state `P`, before the call pushes its return address) -/
structure AtNat (s P : State) (zp zl zc st up ul uc vl : Nat) : Prop where
  pc : P.rip = BitVec.ofNat 64 callNat
  sp : P.regs 4 = s.regs 4 - 200#64
  r5 : P.regs 5 = s.regs 4 - 8#64
  r14 : P.regs 14 = s.regs 14
  fs : P.fsBase = s.fsBase
  x15 : P.xmm 15 = s.xmm 15
  df : P.df = s.df
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 (kq ul vl)
  fr : MemFrame s.mem P.mem (fw s)
  reg : P.mem.regions = s.mem.regions
  sl : Sl s zp zl zc st up ul uc P.mem

end FvModexp.Amd64.Q.NatRem
