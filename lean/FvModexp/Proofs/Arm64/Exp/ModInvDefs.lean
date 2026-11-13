import FvModexp.Proofs.Arm64.Exp.MulHyp
import FvModexp.Proofs.Arm64.Nat.SqrMulX
import FvModexp.Proofs.Arm64.Exp.SubMod2NDefs
import FvModexp.Proofs.Common.ModInvMath
import FvModexp.Proofs.Arm64.NatQ.SqrMulQ

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (go-bigmodexpfix nat.go:1287-1341), arm64 — statement pieces (agent infra)

`z.modularInverseModPowerOfTwo(stk, x, n)`: args `z` X0..X2, `stk` X3, `x` X4..X6, `n` X7. Entry `0x1b6bf0 = 1797104`.
Frame 240 (`MOVD.W R30, -240(RSP)`, FP at `SP - 248`); spills `z.ptr` `SP + 8`, `stk` `SP + 32`, `x` `SP + 40 … + 56`,
`n` `SP + 64` (`above = 72`); locals `SP - 152 … SP - 16` (numWords `SP - 112`, `n + 63` `SP - 40`, `k0` `SP - 88`,
`i` `SP - 80`, `i·64` `SP - 64`, `z` `SP - 16 / - 48 / - 56`, `zz` `SP - 24 / - 128 / - 120`).
Callees at `SP' = SP - 240`: `sqr`, `mul` (stack bound `kc`, a parameter), `trunc`, `lsh`, `subMod2N` (`4608`),
`makeslice`; so `stk = 240 + kc` with `kc ≥ 4608`.

Statement restrictions (all callers: `expNNEven` nat.go:842 `m1.modularInverseModPowerOfTwo(stk, m2, n)`):
`x` normalised and odd (`len(x) > 0`: else `x[0]` panics), `z`'s array apart from `x`'s (so `alias(z, x)` is false),
`1 ≤ n ≤ 2^15`, `len(x) ≤ 2^12`, a non-nil `stk`, `cap z > 0` (`m1 = m1.lsh(natOne, n)` has a word).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes NatOF RtPost StackOK' stWs)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.modularInverseModPowerOfTwo"

theorem fnBase : segAddr LibW.program fn = 1797104 := by decide

/-- bytes above `SP` (the 8 argument spill words + the caller's saved-LR slot) -/
abbrev A : Nat := 72

/-- stack bytes below `SP`: the frame plus the deepest callee (`kc ≥ 4608`, `subMod2N`) -/
@[reducible] def K (kc : Nat) : Nat := 240 + kc

/-- `numWords = ⌈n / 64⌉` (nat.go:1308) -/
@[reducible] def NW (n : Nat) : Nat := (n + 63) / 64

/-- (infra s45) the size bound of `z` at the start of round `j`: `numWords + 1` in the first round (`z = z.make(numWords
+ 1)`; `z.setWord(k0)` does not shorten it — its result is discarded, nat.go:1323), `2^(j-1)` afterwards (`subMod2N` mod
`2^(64·2^(j-1))`) -/
def zB (n j : Nat) : Nat := if j = 1 then NW n + 1 else 2 ^ (j - 1)

theorem zB_one (n : Nat) : zB n 1 = NW n + 1 := by simp [zB]

theorem zB_succ (n : Nat) {j : Nat} (hj : 1 ≤ j) : zB n (j + 1) = 2 ^ j := by
  simp only [zB]; rw [if_neg (by omega), Nat.add_sub_cancel]

theorem zB_le {n j : Nat} (hj : 2 ^ (j - 1) < NW n) : zB n j ≤ NW n + 1 := by
  unfold zB; split <;> omega

theorem zB_mono {n n' : Nat} (h : n ≤ n') (j : Nat) : zB n j ≤ zB n' j := by
  unfold zB; split
  · simp only [NW]; omega
  · exact Nat.le_refl _

/-- (infra s44, TIGHT COSTS) round `j` (`i = 2^j`) charged at its ACTUAL sizes: `zz = zz.sqr(stk, z)` with
`len z ≤ zB n j`, `zz = zz.mul(stk, zz, x[:min(k, len x)])` with `len zz ≤ k` (`k = 2^j` in the loop, `numWords` in the
final round), two `trunc`s, one `lsh`, one `subMod2N` -/
@[reducible] def roundCost (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j k : Nat) : Nat :=
  sqrC (zB n j) + mulC k (min k xl) + 2 * makeCost (2 * NW n + 2) + makeCost (NW n + 2) + SubMod2N.cost n

/-- the loop rounds `1 … r` (`i = 2, 4, …, 2^r`) -/
def sumR (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => sumR sqrC mulC xl n r + roundCost sqrC mulC xl n (r + 1) (2 ^ (r + 1))

theorem sumR_succ (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n r : Nat) :
    sumR sqrC mulC xl n (r + 1) = sumR sqrC mulC xl n r + roundCost sqrC mulC xl n (r + 1) (2 ^ (r + 1)) := rfl

theorem sumR_mono (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n : Nat) {r r' : Nat} (h : r ≤ r') :
    sumR sqrC mulC xl n r ≤ sumR sqrC mulC xl n r' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [sumR_succ]; omega

/-- the budget: the two `make`s, the loop rounds `i = 2, …, < numWords` (at most `⌊log2 numWords⌋` of them), the
final round at `len z ≤ numWords` (infra s43: `log2 + 1` rounds at the final size; s44: per-round sizes) -/
@[reducible] def cost (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n : Nat) : Nat :=
  makeCost (NW n + 1) + makeCost (2 * NW n) + sumR sqrC mulC xl n (Nat.log2 (NW n)) +
    (sqrC (NW n + 1) + mulC (NW n) (min (NW n) xl) + 2 * makeCost (2 * NW n + 2) + makeCost (NW n + 2) +
      SubMod2N.cost n)

/-- the reserve level of the Q-form (`sqr` level twin `stLen + 4·(2·len z) + 64` at `len z ≤ NW + 1`; `mul` needs `8·NW + 64`) -/
@[reducible] def D (n : Nat) : Nat := 8 * NW n + 72

/-- the result value (`k0` masked for `n ≤ 64`) -/
@[reducible] def val (X n : Nat) : Nat := Exp.modularInverseModPowerOfTwo X n

/-- `natOne` (read by `subMod2N`'s final `z.add(z, natOne)`): readable, outside the window, apart from `z`'s array and
from the stack object's header and free part -/
@[reducible] def OneIn (R : RtInv) (L : List (Nat × Nat)) (s : State) (kc zp zc st : Nat) : Prop :=
  ∃ op, NatOne R L s.mem op (win s (K kc) A) ∧ Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
    StkApart s.mem st op 8 ∧ StkApart s.mem st natOneA 24

/-- (s25) divmc's extra `sqr` / `mul` facts at the entry (`StkX` / `OpX` / `CapIn`, Nat/SqrMulX): a non-nil stack whose
header is apart from `runtime.writeBarrier`, the threshold globals `gA` and the free part, the free part apart from `gA`,
`cap = 0 → ptr = 0`, `x`'s whole capacity held, `z` and `x` apart from the free part and `gA` -/
def PX (R : RtInv) (L : List (Nat × Nat)) (s : State) (zp zc st xp xl xc : Nat) : Prop :=
  st ≠ 0 ∧ Apart st 24 StackNat.wbA 4 ∧ Apart st 24 RunIface.gA 32 ∧ Apart st 24 (frP s.mem st) (frN s.mem st) ∧
    Apart (frP s.mem st) (frN s.mem st) RunIface.gA 32 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    CapIn R L xp xl xc ∧ OpX s.mem st zp (8 * zc) ∧ OpX s.mem st xp (8 * xl)

@[reducible] def Pre (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧
    (RunIface.Globals R s.mem (winA s (K kc) A) ∧ Outside RunIface.gA 32 ([(zp, zp + 8 * zc)] ++ stWs s.mem st)) ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ zp < 2 ^ 64 ∧ 0 < zc ∧ WrOut R L s (K kc) A zp zc ∧
    0 < xl ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ RdIn R L s (K kc) A xp xl ∧ NatNorm s.mem xp xl ∧
    natVal s.mem xp xl % 2 = 1 ∧ (0 < zc → Apart zp (8 * zc) xp (8 * xc)) ∧
    StkIn R L s (K kc) A st ∧ stLen s.mem st + 8 * NW n + 72 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st xp (8 * xl) ∧
    (stLen s.mem st + D n ≤ H ∧ cost sqrC mulC xl n ≤ b) ∧
      R.inv (b + stkR H s.mem st) L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ Outside NatAdd.wordT 16 R.rt ∧
    (OneIn R L s kc zp zc st ∧ PX R L s zp zc st xp xl xc)

@[reducible] def Post (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s s' : State) : Prop :=
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = l' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' l' = val (natVal s.mem xp xl) n ∧ NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - cost sqrC mulC xl n + stkR H s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p' c'

end FvModexp.Arm64.ModInv
