import FvModexp.Proofs.Amd64.Top.RunCallees
import FvModexp.Proofs.Common.RunMath

/-!
# `(*bigModExp).Run` (amd64): statement pieces (twin of the arm64 `RunDefs`)

Entry `RSP = e` (return address at `[e]`); prologue `PUSHQ BP; MOVQ SP, BP; SUBQ $0x258, SP` → frame `RSP' = e - 608`, saved `BP`
at `e - 8`, `BP = e - 8`; stack check `e - 480 > stackguard0`; the four argument registers `AX, BX, CX, DI` spilled at
`e + 8 … e + 32` (`above = 40`). The three length headers are read into the stack `big.Int`s at `e - 40`, `e - 72`, `e - 104`
(`neg` byte, then `abs = (ptr, len, cap)`), exactly the arm64 offsets.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

def fn : String := "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run"
/-- `type:errors.errorString` (the `errors.New` allocation). -/
def errT : Nat := Extracted.dataAddr.«type:errors.errorString#8e8100b7»

/-- The stack the call needs below `RSP` (setBytes 4160 + Run's 616, rounded). -/
def stk : Nat := 4800

/-- The value of the `nat` stored at `a` (`(ptr, len, cap)`). -/
@[reducible] def natAt (m : Janus.Arm64.Memory) (a : Nat) : Nat := natVal m (m.readLE a 8) (m.readLE (a + 8) 8)

/-- A header `nat` at `a`: value `v`, normalised, at most four limbs, `len ≤ cap`. -/
def HdrOK (m : Janus.Arm64.Memory) (a v : Nat) : Prop :=
  natAt m a = v ∧ NatNorm m (m.readLE a 8) (m.readLE (a + 8) 8) ∧ m.readLE (a + 8) 8 ≤ 4 ∧
    m.readLE (a + 8) 8 ≤ m.readLE (a + 16) 8

/-- The memory and runtime frame of `Run`'s return (amd64: `g = R14`, window `[RSP - stk, RSP + 40)`; `fsBase` and the
direction flag unchanged). -/
def RunFrame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
    MemFrame s.mem s'.mem (R.rt ++ win s stk 40) ∧ LiveFrame s.mem s'.mem L []

/-- `Run` returned `(nil, err)` with a non-nil `error` (`RAX = RBX = 0`: the nil `[]byte`; `RDI` = the error's type word). -/
def ErrRet (s' : State) : Prop := s'.regs 0 = 0#64 ∧ s'.regs 3 = 0#64 ∧ s'.regs 7 ≠ 0#64

end FvModexp.Amd64.Run
