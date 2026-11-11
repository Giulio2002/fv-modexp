import FvModexp.Proofs.Arm64.Exp.W4En
import FvModexp.Proofs.Arm64.Exp.W4FunO
import FvModexp.Proofs.Arm64.Exp.W4FunV

/-!
# `nat.expNNOddMontgomeryWindowSize4` (arm64): the function-level summary (CONVENTIONS §3)

`ens`: from the entry facts `W4En.EPre` (+ `m` odd, `1 < m`, a stack-length bound and a closed budget) the call
returns `x^y mod m` in `X0..X2` (normalised; the result array is `z`'s or a fresh runtime object), with the live set
extended, the budget reduced by at most `W4Cost`, the stack back at its entry length (array kept or fresh), and memory
changed only in `R.rt`, the frame window (not the caller's saved FP/LR), `z`'s array and the stack's header and free
part. Composed from `W4En.enStep` (entry → `RET`) and the posts of the chain (`EnPost`, `XnPost`, `DivRetPost`, …).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpW4

open FvModexp.Arm64.W4Pro (xjBud xnBudA xnBudAC xnPre Zw)
open FvModexp.Arm64.W4En (EPre EnPost)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4"

/-- the names of the program window-4 is proved on (`LibExp.names`: every function of the exp layer) -/
abbrev names : List String := LibExp.names

/-- the closed budget the precondition asks for (`l` = the stack length at entry, `k = len x - n + 1`) -/
def W4Bud (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + (xjBud n costD (l + StackNat.rnd (23 * n)) +
    (stackNatCost (l + StackNat.rnd (23 * n)) n + xjBud n costD (l + StackNat.rnd (23 * n) + StackNat.rnd n)) +
    xnBudA n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) + xnBudAC n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) +
    xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1))

/-- the cost the postcondition charges -/
def W4Cost (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) + blockSize (8 * n) true +
    stackNatCost (2 ^ 16) (17 * n) + blockSize (8 * (2 * n + 4)) true + makeCost n

/-- the precondition: the entry facts (frame `sp = SP - 928`, window `[sp - K, sp + 1040)`), `m` odd and `> 1`, the
stack-length bound, the budget -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EPre R b L K (s.regs 28).toNat (s.sp.toNat - 928) st zp zc xp xl xc yp ylen mp n mc s ∧
  natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 4 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 17 * n + 68 ≤ 2 ^ 16 ∧
  W4Bud n xl costD (stLen s.mem st) ≤ b

/-- the postcondition (results `X0..X2`) -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ c < 2 ^ 64 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - W4Cost n xl costD (stLen s.mem st) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 928) 112 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st)

theorem buds {n xl costD l b : Nat} (h : W4Bud n xl costD l ≤ b) :
    stackNatCost l (23 * n) + xjBud n costD (l + StackNat.rnd (23 * n)) ≤ b ∧
    stackNatCost l (23 * n) + (stackNatCost (l + StackNat.rnd (23 * n)) n +
      xjBud n costD (l + StackNat.rnd (23 * n) + StackNat.rnd n)) ≤ b ∧
    stackNatCost l (23 * n) + xnBudA n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b ∧
    stackNatCost l (23 * n) + xnBudAC n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b ∧
    stackNatCost l (23 * n) + xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b := by
  unfold W4Bud at h; omega

theorem bud_fin {b b1 bd b2 b' b'' s0 P bs8 iff17 snc17 bsz mk n : Nat} (hb1 : b - s0 ≤ b1) (hbd : b1 - P ≤ bd)
    (hb3 : bd - (iff17 + snc17) ≤ b2) (hb5 : b2 - bsz ≤ b') (hb8 : b' - mk ≤ b'') (hif : iff17 ≤ bs8)
    (hs : snc17 ≤ stackNatCost (2 ^ 16) (17 * n)) :
    b - (s0 + P + bs8 + stackNatCost (2 ^ 16) (17 * n) + bsz + mk) ≤ b'' := by omega

theorem snc_mono {l n : Nat} (h : l ≤ 2 ^ 16) : stackNatCost l n ≤ stackNatCost (2 ^ 16) n := by
  unfold stackNatCost allocCost; omega

theorem if_le (n : Nat) : (if 4 < n then blockSize (8 * n) true else 0) ≤ blockSize (8 * n) true := by
  split <;> omega

end FvModexp.Arm64.ExpW4
