import FvModexp.Proofs.Arm64.Exp.IExpCl
import FvModexp.Proofs.Arm64.Top.ExpBudOKB

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64), every callee proved AND the cost facts discharged: `IExp.ensClB` (agent expmc s42)

`IExp.ensCl` with its last non-runtime premise `BudCl` proved for the CURRENT `RunIface.ExpBudget` (with the temporary
`2^32` slack, see BRIEF "TIGHT COSTS"): divmc's crude bound `ExpBud.main` (both left sides `≤ 7·10^14 + 4.2·10^13 · yl`)
against `ExpBudget w yl ≥ (512 yl + 128) · opCost 1 · 2^32` (`w ≥ n ≥ 1`). The same step as divmc's draft
`scripts/gen/ExpBudOK.lean.draft` (adapted to the `min w 1` factor). When the slack is removed, only `budCl` changes
(the tight bound needs the Q-form costs of every owner; numeric mirror scripts/gen/exp-budget-check.py --target).
Remaining premises of `ensClB`: the Janus runtime contracts only (window depths fixed as top's `Run.Closed.expC`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.IExp

theorem expBudget_ge (w yl : Nat) (hw : 1 ≤ w) :
    700000000000000 + 42000000000000 * yl ≤ RunIface.ExpBudget w yl := by
  have ho : 4120 ≤ RunIface.opCost w := by unfold RunIface.opCost allocCost; omega
  have h1 := Nat.mul_le_mul_left (8 * (64 * yl) + 128) ho
  rw [Nat.mul_comm (8 * (64 * yl) + 128) 4120] at h1
  have h2 := Nat.mul_le_mul_right (2 ^ 32) h1
  rw [Nat.mul_comm (4120 * (8 * (64 * yl) + 128)) (2 ^ 32)] at h2
  have hm : min w 1 = 1 := by omega
  unfold RunIface.ExpBudget
  rw [hm, Nat.mul_one, Nat.mul_comm ((8 * (64 * yl) + 128) * RunIface.opCost w) (2 ^ 32)]
  simp only [show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
  omega

/-- **the closed budget bound** for the current `RunIface.ExpBudget` -/
theorem budCl : BudCl := by
  intro xl yl n lm hx hy hn0 hn hlm
  obtain ⟨h1, h2⟩ := ExpBud.main xl yl n lm hx hy hn0 hn hlm
  have hB := expBudget_ge (max (max xl yl) n) yl (by omega)
  exact ⟨Nat.le_trans h1 hB, Nat.le_trans h2 hB⟩

set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it (`ExpSpecM`), every machine-code callee proved, every cost fact proved:
premises = the Janus runtime contracts only. Windows: outer `nat.expNN` at `71312`, `expNNEven` at `72368`, inner
`nat.expNN` at `70720`; `(*Int).exp`'s window `72944 ≤ stk`. -/
theorem ensClB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {stk above : Nat} (hK : 72944 ≤ stk) (hab : 48 ≤ above) :
    ExpSpecM impl R stk above :=
  ensCl impl hap R hmk hgr hmc hmv hmz hno hwb hget hput (K := 71312) (KN := 70720) (stkE := 72368)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) hab budCl

end FvModexp.Arm64.IExp
