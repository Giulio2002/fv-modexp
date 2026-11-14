import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64, nat.go:906): definitions (agent asm s66; amd64 twin of infra's arm64 `P2DDefs`)

Code map (fn `0x5e8fa0`, segment `seg22`, 793 bytes; frame `0x70`: `PUSHQ BP; MOVQ SP, BP; SUBQ $0x68, SP`, so
`sp = RSP_entry - 0x70`, `[sp + 0x70]` = return address, `[sp + 0x68]` = saved BP, `BP = sp + 0x68`; no defer).
Arguments: `z = (AX, BX, CX)`, `stk = DI`, `x = (SI, R8, R9)`, `y` on the stack (`sp + 0x78 / 0x80 / 0x88`),
`logM = R10`. Entry spills `[sp + 0x90] := AX`, `[sp + 0xb0] := SI`.
* `len y = 0` / `len y = 1 ∧ y[0] = 0` → `gopanic` (excluded: `0 < Y`, `y` normalised); `len x = 0` → `panicBounds`
  (excluded: `0 < X`).
* `logM = 1` (`oneE = 0x5e90e1`): `z.setWord(x[0] & 1)`: bit 0 → `BX = 0`; bit 1 → `cap z ≠ 0`: `[AX] = 1`, else
  `makeslice(Word, 1, 1)` (return `0x5e910d`).
* `x` odd (`oddE = 0x5e902d`): `logM ≥ 48 ∧ bitLen y ≥ 48` → `expNNPowerOfTwoWindowSize4` (return `0x5e90b9`), else
  window 2 (return `0x5e90da`); `y` is re-stored at `[sp] / [sp + 8] / [sp + 0x10]`.
* `x` even, `len y > 1` → `z[:0]` (`zeroE = 0x5e9025`); `len y = 1`: the `trailingZeroBits` loop (`tzH = 0x5e912f`,
  `R12 = i`), `tz · y[0]` (`MULQ`): overflow or `≥ logM` → `z[:0]` (`0x5e916a`); else spills, `rsh(nil, x, tz)`
  (return `0x5e91b7`), the recursive `expNNPowerOfTwo(z, stk, xOdd, y, logM - lo)` (return `0x5e9215`),
  `z.lsh(z, lo)` (return `0x5e9228`, then `RET`).

Costs (same as arm64): `costO c2 c4 l yl lm` (odd base: either window or the `logM = 1` allocation), `costP` (any base:
the odd cost maximised over `logM' ≤ logM` (`supTo`), plus the `rsh`/`lsh` allocations).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

abbrev fnE : Nat := 0x5e8fa0
theorem fnE_eq : segAddr Extracted.program NHyp.fnP2 = fnE := by decide

/-- `max_{j ≤ n} f j` -/
def supTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (supTo f n) (f (n + 1))

theorem le_supTo (f : Nat → Nat) : ∀ n j, j ≤ n → f j ≤ supTo f n := by
  intro n
  induction n with
  | zero => intro j hj; rw [show j = 0 by omega]; exact Nat.le_refl _
  | succ n ih =>
    intro j hj
    simp only [supTo]
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact Nat.le_trans (ih j (by omega)) (Nat.le_max_left _ _)
    · rw [show j = n + 1 by omega]; exact Nat.le_max_right _ _

/-- the budget on an odd base (`c2`/`c4`: the window costs at stack level `l`); Go calls exactly ONE window
(nat.go:960-966), so the path MAX of the two -/
@[reducible] def costO (c2 c4 : Nat → Nat → Nat → Nat) (l yl lm : Nat) : Nat :=
  max (c2 l yl lm) (c4 l yl lm) + allocCost 8

/-- the budget on any positive base -/
@[reducible] def costP (c2 c4 : Nat → Nat → Nat → Nat) (l xl yl lm : Nat) : Nat :=
  supTo (costO c2 c4 l yl) lm + makeCost (xl + 2) + makeCost (lm / 64 + 2)

/-- the stack need (the windows' `2^13`) -/
@[reducible] def needP : Nat → Nat → Nat → Nat := fun _ _ _ => 2 ^ 13

/-- the precondition (= `NHyp.P2Hyp`'s, on natural numbers; window `[RSP - stk, RSP + A)`) -/
@[reducible] def PreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk A cst zp zl zc st xp xl yp yl lm : Nat)
    (s : State) : Prop :=
  NHyp.CPre R b L stk A zp zl zc st [(xp, xl), (yp, yl)] (2 ^ 13) cst s ∧
    0 < natVal s.mem xp xl ∧ 0 < natVal s.mem yp yl ∧ 1 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      NHyp.StkApart s.mem st op 8

/-- the registers at the entry (`y` on the stack) -/
@[reducible] def Regs (s : State) (zp zl zc st xp xl xc yp yl yc lm : Nat) : Prop :=
  s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
    s.regs 7 = BitVec.ofNat 64 st ∧ s.regs 6 = BitVec.ofNat 64 xp ∧ s.regs 8 = BitVec.ofNat 64 xl ∧
    s.regs 9 = BitVec.ofNat 64 xc ∧ s.regs 10 = BitVec.ofNat 64 lm ∧ NHyp.StkArg s 0 yp yl yc

/-- the postcondition (callee-saved registers + `NHyp.CPostR`) -/
@[reducible] def PostD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk A cst zp zc st v : Nat) (s s' : State) :
    Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    NHyp.CPostR R b L stk A zp zc st v cst s s'

set_option maxRecDepth 20000 in
/-- a return address inside the function (`seg22`) is a return address of every callee program without it -/
theorem ra_p2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains NHyp.fnP2 = false) (i : Nat) (hi : i < 793) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (fnE + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg22) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg22.name = NHyp.fnP2 by decide]; exact hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e8fa0 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg22] using this

end FvModexp.Amd64.P2D
