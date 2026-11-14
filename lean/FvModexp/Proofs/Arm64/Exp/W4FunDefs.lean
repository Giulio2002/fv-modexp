import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4Anc
import FvModexp.Proofs.Arm64.Exp.W4EnPre

/-!
# window-4 (arm64): the function summary's definitions (`Pre`/`Post`, budgets)

Hoisted (s67) out of `W4Fun`, `W4XnJ` and `W4XnS` (unchanged text, same namespaces) so that the witness (`W4Wit`) and
the modules that only state these definitions do not import the proofs (row import-chain cut).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

/-- the budget of window-4 from `xJ` on (stack level `l`) -/
@[reducible] def xjBud (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) +
    (costD + (blockSize (8 * n) true + stackNatCost (l + 2 * StackNat.rnd (2 * n)) (17 * n) +
      blockSize (8 * (2 * n + 4)) true))))

/-- the budget of path A from `xnE` (stack level `l0`, `k = len x - n + 1`) -/
@[reducible] def xnBudA (n costD l0 k : Nat) : Nat :=
  stackNatCost l0 k + (stackNatCost (l0 + StackNat.rnd k) n + (costD +
    (stackNatCost (l0 + StackNat.rnd k + StackNat.rnd n) n +
      xjBud n costD (l0 + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n))))

/-- the same bound for the join's path C (a lower level, no extra `stk.nat`) -/
@[reducible] def xnBudAC (n costD l0 k : Nat) : Nat :=
  stackNatCost l0 k + (stackNatCost (l0 + StackNat.rnd k) n + (costD +
    xjBud n costD (l0 + StackNat.rnd k + StackNat.rnd n)))

end FvModexp.Arm64.W4Pro

namespace FvModexp.Arm64.ExpW4

open FvModexp.Arm64.W4Pro (xjBud xnBudA xnBudAC xnPre)
open FvModexp.Arm64.W4En (EPre)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4"

/-- the names of the program window-4 is proved on (`LibW.names`: every function of the exp layer) -/
abbrev names : List String := LibW.names

/-- the closed budget the precondition asks for (`l` = the stack length at entry, `k = len x - n + 1`): the entry
`stk.nat` plus the MAXIMUM over the paths (TIGHT COSTS, expmc s42; was their sum) -/
def W4Bud (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + max (max (xjBud n costD (l + StackNat.rnd (23 * n)))
    (stackNatCost (l + StackNat.rnd (23 * n)) n + xjBud n costD (l + StackNat.rnd (23 * n) + StackNat.rnd n)))
    (max (max (xnBudA n costD (l + StackNat.rnd (23 * n)) (xl - n + 1)) (xnBudAC n costD (l + StackNat.rnd (23 * n)) (xl - n + 1)))
      (xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1)))

/-- the stack level bound at the window's last `stk.nat` (`zz`'s scratch, after `x`'s normalisation and the `RR`
section): entry `l`, `stk.reserve(23n)`, path A's `q`/`z2` (`len x - n + 1`, `n`), path B's `n`, two `2n` scratches -/
@[reducible] def lvT (n xl l : Nat) : Nat :=
  l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n + 2 * StackNat.rnd (2 * n)

/-- the cost the postcondition charges (TIGHT COSTS, expmc s42: the last `stk.nat` at the level bound `lvT`, was `2^16`) -/
def W4Cost (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) + blockSize (8 * n) true +
    stackNatCost (lvT n xl l) (17 * n) + blockSize (8 * (2 * n + 4)) true + makeCost n

/-- the precondition: the entry facts (frame `sp = SP - 928`, window `[sp - K, sp + 1040)`), `m` odd and `> 1`, the
stack-length bound, the budget -/
def PreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EPre R b L K (s.regs 28).toNat (s.sp.toNat - 928) st zp zc xp xl xc yp ylen mp n mc s ∧ st ≠ 0 ∧
  natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧
  W4Bud n xl costD (stLen s.mem st) ≤ b

/-- the postcondition (results `X0..X2`) -/
def PostD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - W4Cost n xl costD (stLen s.mem st) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 928) 112 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the division cost the window charges, from `nat.div`'s level-dependent cost `costF` (`l` = the stack length at
entry): the MAXIMUM (TIGHT COSTS, expmc s42; was the sum) of `x mod m` (when `len x > n`) and the `RR` division
on its four possible stack levels -/
def divCost (costF : Nat → Nat → Nat → Nat) (n xl l : Nat) : Nat :=
  max (max (costF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n)
    (costF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (2 * n + 1) n))
  (max (max (costF (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n)
    (costF (l + StackNat.rnd (23 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n))
    (costF (l + StackNat.rnd (23 * n) + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n))

/-- the precondition (see `PreD`), with the division cost `divCost costF` -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) : Prop :=
  PreD R b L K (divCost costF n xl (stLen s.mem st)) zp zc st xp xl xc yp ylen mp n mc s

/-- the postcondition (see `PostD`), with the division cost `divCost costF` -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (zp zc st xp xl yp ylen mp n : Nat) (s s' : State) : Prop :=
  PostD R b L K (divCost costF n xl (stLen s.mem st)) zp zc st xp xl yp ylen mp n s s'

end FvModexp.Arm64.ExpW4
