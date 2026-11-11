import FvModexp.Proofs.Arm64.Top.RunCallees
import FvModexp.Proofs.Common.RunMath

/-!
# `(*bigModExp).Run` (arm64): statement pieces

Frame: `SUB $624` with the frame record at `SP' - 8` / `SP'` (`SP' = SP - 624`), stack check `SP - 496 > stackguard0`,
the four argument words spilled at `SP + 8 … SP + 40` (`above = 40`). The three length headers are read into the stack
`big.Int`s `A` (`SP - 40`), `B` (`SP - 72`), `C` (`SP - 104`): `neg` byte, then `abs = (ptr, len, cap)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

def fn : String := "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run"
/-- `type:errors.errorString` (the `errors.New` allocation). -/
def errT : Nat := Extracted.dataAddr.«type:errors.errorString#8e8100b7»

/-- The stack the call needs below `SP` (setBytes 4160 + Run's 624, rounded); the big callees' depth is added when they land. -/
def stk : Nat := 4800

/-- The value of the `nat` stored at `a` (`(ptr, len, cap)`). -/
@[reducible] def natAt (m : Memory) (a : Nat) : Nat := natVal m (m.readLE a 8) (m.readLE (a + 8) 8)

/-- A header `nat` at `a` (the `abs` field of a stack `big.Int`): value `v`, normalised, at most four limbs, `len ≤ cap`. -/
def HdrOK (m : Memory) (a v : Nat) : Prop :=
  natAt m a = v ∧ NatNorm m (m.readLE a 8) (m.readLE (a + 8) 8) ∧ m.readLE (a + 8) 8 ≤ 4 ∧
    m.readLE (a + 8) 8 ≤ m.readLE (a + 16) 8

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The memory and runtime frame of `Run`'s return: the live set grows by objects of the runtime, the budget drops by at most
`B`, the invariant holds, only `R.rt` and the window changed, and the caller's live objects are intact. -/
def RunFrame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (s s' : State) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
    MemFrame s.mem s'.mem (R.rt ++ win s stk 40) ∧ LiveFrame s.mem s'.mem L []

/-- `Run` returned `(nil, err)` with a non-nil `error` (`X0, X1 = 0`: the nil `[]byte`; `X3` = the error's type word). -/
def ErrRet (s' : State) : Prop := s'.regs 0 = 0#64 ∧ s'.regs 1 = 0#64 ∧ s'.regs 3 ≠ 0#64

end FvModexp.Arm64.Run
