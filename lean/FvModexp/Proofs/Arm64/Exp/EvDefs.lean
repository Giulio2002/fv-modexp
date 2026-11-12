import FvModexp.Proofs.Arm64.Exp.LibNE
import FvModexp.Proofs.Common.TzWord

set_option autoImplicit false

/-!
# `nat.expNNEven` (go-bigmodexpfix nat.go:801-847), arm64 — code map (agent infra)

Entry `0x1b4f70 = 1789808`, args `z` X0..X2, `stk` X3, `x` X4..X6, `y` X7..X9, `m` X10..X12. Program: `LibNE`
(= `LibN` ∪ {expNNEven, expNNEven.deferwrap1}; NESTED-PROGRAM RULE: no `(*Int).exp`, no Run).
Frame: guard `SUB $208` (`BLS` → `morestack`), `SUB $336` → `SP' = SP - 336` (segment lemmas use `sp := SP'`), saved
FP at `sp - 8`, LR at `sp`. Spills (caller area, `sp + 344 ..`): 344 zp, 360 zc, 368 st, 376 xp, 384 xl, 392 xc,
400 yp, 408 yl, 416 yc, 424 mp, 432 ml, 440 mc (`zl` is not spilled). Locals: byte 127 defer bit; 184 `n = tz(m)`;
224 temp (`ml - n/64`, then `2·max`); m1 = (288, 208, 216); m2 = (280, 192, 200); z1 = (264, 152, 160);
z2 = (256, 136, 144); z after `set` = (272, 168, 176); result 232/240/248; defer closure record at 296
(`= deferwrap1`), 304 `st`, 312 saved `len`; 320 = `sp + 296`.

Code map (`fn + 4·idx`):
* prologue, spills, `CBZ ml` (`ml = 0` → `n = 0`; excluded by `0 < M`), `tz` loop (`tzH` = 0x1b52f8: `i < ml`, first
  non-zero word, `RBIT; CLZ`; `panicBounds` (`pbE`) iff no non-zero word — excluded), join `enS` (0x1b4fd8, R1 = n).
* `m1 = stk.nat(n/64 + 1)` (ret `nat1R`) · `m1 = m1.lsh(natOne, n)` (`natOne` = rodata `[R27+16]`, ret `lshR`) ·
  `m2 = stk.nat(ml - n/64)` (`nat2R`) · `m2 = m2.rsh(m, n)` (`rshR`) · `z1 = stk.nat(2·max(len m1, len m2))` (`nat3R`) ·
  `z1 = z1.expNN(stk, x, y, m1, false)` (`exp1R`) · `z2 = stk.nat(same)` (`nat4R`) · `z2 = z2.expNN(…, m2, false)`
  (`exp2R`) · `z = z.set(z2)`: `len z2 ≤ cap z` → reuse `zp`; else `makeslice(1,1)` (`mk1R`) /
  `makeslice(l, l+4)` (`mkNR`); join `setJ`; `memmove` unless same pointer (ret `mvR`) · `z1 = z1.subMod2N(z1, z2, n)`
  (`smR`) · `m2inv = m1.modularInverseModPowerOfTwo(stk, m2, n)` (`miR`) · `z2 = z2.mul(stk, z1, m2inv)` (`mul1R`) ·
  `z2 = z2.trunc(z2, n)` (`trR`) · `t = z1.mul(stk, z2, m2)` (`mul2R`) · `z = z.add(z, t)` (`addR`) · deferred
  `stk.restore(len)` via `CALL (R10)` (`R26 = sp + 296`, ret `dwR`) → `LDP`/`RET`.
-/

namespace FvModexp.Arm64.ExpEven

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven"
def fnDw : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1"

/-- the function's program -/
abbrev names : List String := LibNE.names

theorem fnBase : segAddr LibNE.program fn = 1789808 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 1789808
/-- `nat.expNNEven.deferwrap1` -/
abbrev dwE : Nat := 1790848
/-- the join after the `tz` loop (`MOVD R3, 368(RSP)`, R1 = n) -/
abbrev enS : Nat := 1789912
/-- the `tz` loop head (`CMP R1, R11`) / increment (`ADD $1, R1, R1`) / `panicBounds` -/
abbrev tzH : Nat := 1790712
abbrev tzI : Nat := 1790708
abbrev pbE : Nat := 1790744
/-- the first `stk.nat` call and the return addresses of every call (join points) -/
abbrev nat1C : Nat := 1789992
abbrev nat1R : Nat := 1789996
abbrev lshR : Nat := 1790024
abbrev nat2R : Nat := 1790048
abbrev rshR : Nat := 1790068
abbrev nat3R : Nat := 1790108
abbrev exp1R : Nat := 1790156
abbrev nat4R : Nat := 1790180
abbrev exp2R : Nat := 1790228
abbrev mk1R : Nat := 1790296
abbrev mkNR : Nat := 1790344
abbrev setJ : Nat := 1790368
abbrev mvR : Nat := 1790412
abbrev smR : Nat := 1790468
abbrev miR : Nat := 1790516
abbrev mul1R : Nat := 1790560
abbrev trR : Nat := 1790580
abbrev mul2R : Nat := 1790624
abbrev addR : Nat := 1790664
abbrev dwR : Nat := 1790688

/-- `n/64 + 1` words of `m1` (`(n + _W) / _W`) and `ml - n/64` words of `m2` -/
@[reducible] def a1 (n : Nat) : Nat := n / 64 + 1
@[reducible] def a2 (ml n : Nat) : Nat := ml - n / 64

end FvModexp.Arm64.ExpEven
