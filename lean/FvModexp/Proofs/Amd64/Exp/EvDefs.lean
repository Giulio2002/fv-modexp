import FvModexp.Proofs.Amd64.Exp.LibNE
import FvModexp.Proofs.Common.TzWord

set_option autoImplicit false

/-!
# `nat.expNNEven` (go-bigmodexpfix nat.go:801-847), amd64 — code map (asm s55; twin of infra's Arm64/Exp/EvDefs.lean)

Entry `0x5e8280 = 6193792`. Go ABIInternal: register args `z = (zp, zl, zc)` RAX/RBX/RCX, `stk = st` RDI,
`x = (xp, xl, xc)` RSI/R8/R9; `y` and `m` do not fit the remaining registers and are passed on the stack:
`y = (yp, yl, yc)` at `RSP + 8/16/24`, `m = (mp, ml, mc)` at `RSP + 32/40/48` (entry `RSP`). Program: `LibNE`
(= `LibN` ∪ {expNNEven, expNNEven.deferwrap1}; NESTED-PROGRAM RULE: no `(*Int).exp`, no Run).

Frame: guard `LEAQ -0xc8(SP), R12; CMPQ R12, 16(R14); JBE morestack` (`msA`), `PUSHQ BP; MOVQ SP, BP;
SUBQ $0x140, SP` → `sp := RSP_entry - 0x148` (segment lemmas use `sp`); saved RBP at `sp + 0x140`, return address at
`sp + 0x148`. Caller area (`sp + 0x150 ..`): stack args y 0x150/0x158/0x160, m 0x168/0x170/0x178; register spills
0x180 zp, 0x190 zc, 0x198 st, 0x1a0 xp, 0x1a8 xl, 0x1b0 xc (`zl` not spilled). Locals (`sp + k`): byte 0x77 defer bit;
0x78 temp (`len z2 + 4`); z2 = (p 0xf8, l 0x80, c 0x88); z1 = (0x100, 0x90, 0x98); z after `set` = (0x108, 0xa0, 0xa8);
0xb0 `n = tz(m)`; m2 = (0x110, 0xb8, 0xc0); m1 = (0x118, 0xc8, 0xd0); 0xd8 temp (`ml - n/64`, then `2·max`); result
0xe0/0xe8/0xf0 (zeroed at entry); defer record 0x120 (`= deferwrap1`), 0x128 `st`, 0x130 saved `len`; 0x138 = `sp + 0x120`
(X15 = 0 stored there first). Callees' stack arguments at `sp + 0 ..`.

Code map (`fnE + off`):
* +0x00 prologue, spills, defer bit 0, result zeroed; `ml = [sp+0x170]`: `ml = 0` → `n = 0` (excluded by `0 < M`) else
  `tz` loop (R10 = mp, BX = i; head `tzH`: `CMPQ DX(ml), BX; JBE pbE`; word `[R10 + 8i]`; zero → `tzI` (`INCQ BX`);
  non-zero → `BX = 64i + BSF`) → join `enS` (+0x87, BX = n, DI = st).
* `enS`: st spill, n spill (0xb0), `CX = (n + 64) >> 6` (`a1`), `0xd8 = ml - n/64` (`a2`, SAR-rounded: n ≥ 0), the
  defer record (`DX = stk.len`), defer bit 1 → `m1 = stk.nat(a1)` (`nat1C`, ret `nat1R`) · `m1 = m1.lsh(natOne, n)`
  (`natOne` header words from `.data`, ret `lshR`) · `m2 = stk.nat(a2)` (`nat2R`) · `m2 = m2.rsh(m, n)` (`rshR`) ·
  `z1 = stk.nat(2·max(len m1, len m2))` (`CMOVG`, `nat3R`) · `z1 = z1.expNN(stk, x, y, m1, false)` (y, m1 as stack
  args at `sp + 0 .. 0x28`, R10 = 0; `exp1R`) · `z2 = stk.nat(same)` (`nat4R`) · `z2 = z2.expNN(…, m2, false)`
  (`exp2R`) · `z = z.set(z2)` (`setT`): `len z2 ≤ zc` → reuse `zp` (`JG` not taken); else `len z2 = 1` →
  `makeslice(1, 1)` (`mk1R`), or `makeslice(l, l + 4)` (`mkNR`); join `setJ` (DI = p, BX = l, DX = c, SI = len z2,
  AX = z2.p, CX = z2.c); `memmove(p, z2.p, 8·min)` unless `p = z2.p` (ret `mvR`); join `mvJ` ·
  `z1 = z1.subMod2N(z1, z2, n)` (n as stack arg at `sp`; `smR`) · `m2inv = m1.modularInverseModPowerOfTwo(stk, m2, n)`
  (R10 = n; `miR`) · `z2 = z2.mul(stk, z1, m2inv)` (m2inv as stack args; `mul1R`) · `z2 = z2.trunc(z2, n)` (`trR`) ·
  `t = z1.mul(stk, z2, m2)` (`mul2R`) · `z = z.add(z, t)` (`addR`) → result spill, defer bit 0, deferred
  `stk.restore(len)` via `CALL R12` (`R12 = [sp + 0x120]`, DX = `sp + 0x120`; ret `dwR`) → result regs, `ADDQ $0x140`,
  `POPQ BP`, `RET` (`retA`).
* `deferwrap1` (`dwE`): `AX = [DX+16]` (len), `CX = [DX+8]` (st), `[CX+16]` (cap) `< len` → `panicBounds`; else
  `[CX+8] = len`; `RET`.
-/

namespace FvModexp.Amd64.ExpEven

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic FvModexp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven"
def fnDw : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1"

/-- the function's program -/
abbrev names : List String := LibNE.names

theorem fnBase : segAddr LibNE.program fn = 6193792 := by decide
theorem dwBase : segAddr LibNE.program fnDw = 6195392 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 6193792
/-- `nat.expNNEven.deferwrap1` -/
abbrev dwE : Nat := 6195392
/-- the join after the `tz` loop (`MOVQ DI, 0x198(SP)`, BX = n) -/
abbrev enS : Nat := 6193927
/-- the `tz` loop increment (`INCQ BX`) / head (`CMPQ DX, BX`) / `panicBounds` -/
abbrev tzI : Nat := 6195221
abbrev tzH : Nat := 6195224
abbrev pbE : Nat := 6195254
/-- the first `stk.nat` call and the return addresses of every call (join points) -/
abbrev nat1C : Nat := 6194042
abbrev nat1R : Nat := 6194047
abbrev lshR : Nat := 6194085
abbrev nat2R : Nat := 6194130
abbrev rshR : Nat := 6194167
abbrev nat3R : Nat := 6194231
abbrev exp1R : Nat := 6194348
abbrev nat4R : Nat := 6194393
abbrev exp2R : Nat := 6194510
/-- `z.set(z2)`: the capacity test, the two `makeslice` returns, the join, the `memmove` return and its join -/
abbrev setT : Nat := 6194535
abbrev mk1R : Nat := 6194588
abbrev mkNR : Nat := 6194648
abbrev setJ : Nat := 6194683
abbrev mvR : Nat := 6194737
abbrev mvJ : Nat := 6194761
abbrev smR : Nat := 6194821
abbrev miR : Nat := 6194917
abbrev mul1R : Nat := 6194992
abbrev trR : Nat := 6195014
abbrev mul2R : Nat := 6195098
abbrev addR : Nat := 6195145
abbrev dwR : Nat := 6195188
/-- the `RET` of the normal exit / the `morestack` path -/
abbrev retA : Nat := 6195220
abbrev msA : Nat := 6195302

/-- the frame size below the entry `RSP` (`PUSHQ BP` + `SUBQ $0x140`): `sp = RSP_entry - fr` -/
abbrev fr : Nat := 0x148

/-- `(n + 64) / 64` words of `m1` and `ml - n/64` words of `m2` (as arm64) -/
@[reducible] def a1 (n : Nat) : Nat := n / 64 + 1
@[reducible] def a2 (ml n : Nat) : Nat := ml - n / 64

end FvModexp.Amd64.ExpEven
