import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.CallW

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64, nat.go:906): definitions (agent infra)

Code map (fn `0x1b5920 = 1792288`, segment `seg22`; frame 112: `MOVD.W R30, -112(RSP)`, `SP' = SP - 112`, `[SP'] = LR`,
`[SP' - 8] = FP`; no defer):
* entry spills `120 := z.ptr`, `152 := x.ptr`, `176 := y.ptr` (i.e. `SP + 8, 40, 64`); `len y = 0` / `len y = 1 ∧ y[0] = 0`
  → `gopanic` (excluded: `0 < Y`, `y` normalised); `len x = 0` → `panicBounds` (excluded: `0 < X`).
* `logM = 1` (`0x1b59f0`): `z.setWord(x[0] & 1)`: bit 0 → `z[:0]`; bit 1 → `cap z ≠ 0`: `z[0] = 1`, else
  `makeslice(Word, 1, 1)` (return `1792544`).
* `x` even, `len y > 1` → `z[:0]` (`0x1b5980`); `len y = 1`: the `trailingZeroBits` loop (`0x1b5a44`), `tz · y[0]`
  (`MUL`/`UMULH`): overflow or `≥ logM` → `z[:0]`; else spills, `rsh(nil, x, tz)` (return `1792716`), the recursive
  `expNNPowerOfTwo(z, stk, xOdd, y, logM - lo)` (return `1792772`), `z.lsh(z, lo)` (return `1792792`).
* `x` odd: `logM ≥ 48 ∧ bitLen y ≥ 48` → `expNNPowerOfTwoWindowSize4` (return `1792468`), else window 2 (return `1792484`).

Costs: `costO c2 c4 ℓ yl lm` (odd base: either window or the `logM = 1` allocation), `costP` (any base: the odd cost
maximised over `logM' ≤ logM` (`supTo`, no monotonicity premise needed), plus the `rsh`/`lsh` allocations).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

abbrev fnE : Nat := 1792288
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

/-- the budget on an odd base (`c2`/`c4`: the window costs at stack level `ℓ`). TIGHT COSTS (infra s45): Go calls
exactly ONE window (nat.go:1105-1109), so the path MAX of the two (was their sum) -/
@[reducible] def costO (c2 c4 : Nat → Nat → Nat → Nat) (ℓ yl lm : Nat) : Nat :=
  max (c2 ℓ yl lm) (c4 ℓ yl lm) + allocCost 8

/-- the budget on any positive base -/
@[reducible] def costP (c2 c4 : Nat → Nat → Nat → Nat) (ℓ xl yl lm : Nat) : Nat :=
  supTo (costO c2 c4 ℓ yl) lm + makeCost (xl + 2) + makeCost (lm / 64 + 2)

/-- the stack need (the windows' `2^13`) -/
@[reducible] def needP : Nat → Nat → Nat → Nat := fun _ _ _ => 2 ^ 13

/-- the precondition (= `NHyp.P2Hyp`'s, on natural numbers; window `[SP - stk, SP + A)`) -/
@[reducible] def PreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk A cst zp zl zc st xp xl yp yl lm : Nat)
    (s : State) : Prop :=
  NHyp.CPre R b L stk A zp zl zc st [(xp, xl), (yp, yl)] (2 ^ 13) cst s ∧
    0 < natVal s.mem xp xl ∧ 0 < natVal s.mem yp yl ∧ 1 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      EvenHyp.StkApart s.mem st op 8

/-- the registers at the entry -/
@[reducible] def Regs (s : State) (zp zl zc st xp xl xc yp yl yc lm : Nat) : Prop :=
  s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧
    s.regs 3 = BitVec.ofNat 64 st ∧ s.regs 4 = BitVec.ofNat 64 xp ∧ s.regs 5 = BitVec.ofNat 64 xl ∧
    s.regs 6 = BitVec.ofNat 64 xc ∧ s.regs 7 = BitVec.ofNat 64 yp ∧ s.regs 8 = BitVec.ofNat 64 yl ∧
    s.regs 9 = BitVec.ofNat 64 yc ∧ s.regs 10 = BitVec.ofNat 64 lm

/-- the postcondition (callee-saved registers + `NHyp.CPostR`) -/
@[reducible] def PostD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk A cst zp zc st v : Nat) (s s' : State) :
    Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    NHyp.CPostR R b L stk A zp zc st v cst s s'

set_option maxRecDepth 20000 in
/-- a return address inside the function (`seg22`) is a return address of every callee program without it -/
theorem ra_p2 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains NHyp.fnP2 = false) (i : Nat) (hi : i < 157) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (1792288 + 4 * i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg22) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x1b5920 + 4 * i < 2 ^ 48; omega) (by decide)
  simpa only [Extracted.seg22] using this

end FvModexp.Arm64.P2D
