import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.EnsWiden
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Lsh
import FvModexp.Proofs.Arm64.Nat.Rsh
import FvModexp.Proofs.Arm64.Nat.Trunc
import FvModexp.Proofs.Arm64.Nat.SqrWX
import FvModexp.Proofs.Arm64.Nat.MulDefs

set_option autoImplicit false

/-!
# The exp layer (arm64): CLOSED callee summaries for infra's rows, without the old `nat.sqr` / `nat.mul` (agent infra;
split s54 so the Q-form rows do not compile the retired old SCCs; `sq` / `mu` stay in `CalleeInst`)

`nsP` = the functions of the directly summarised callees of `expNNPowerOfTwoWindowSize2/4`, `expNNPowerOfTwo` and
`modularInverseModPowerOfTwo`:
`(*stack).nat` (divmc `StackNat.ensL`), `nat.sqr` (divmc `NatSqr.hypX`, cost `sqrC`, window `sqrWX`), `nat.mul`
(`NatMul.hypX`, cost `mulC`, window `mulWX`), `nat.trunc` (asm `Trunc.ens`), `nat.rsh` / `nat.lsh` (`Rsh.ens`,
`Lsh.ens`). Each summary is moved to `nsP` with `EnsWiden.ens_widen`. Used by `P2W2Row`, `P2W4Row`, `P2DRow`, `ModInvRow`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)

namespace FvModexp.Arm64.CalleeInst

open FvModexp.Arm64.EvenHyp

def nsP : List String :=
  StackNat.names ++ NatSqr.names ++ NatMul.names ++ Trunc.names ++ Rsh.names ++ Lsh.names

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

set_option maxHeartbeats 64000000 in
theorem sub : ∀ x, nsP.contains x = true → LibW.names.contains x = true := sub_of_all (by decide)

set_option maxHeartbeats 64000000 in
theorem subs : (∀ x, StackNat.names.contains x = true → nsP.contains x = true) ∧
    (∀ x, NatSqr.names.contains x = true → nsP.contains x = true) ∧
    (∀ x, NatMul.names.contains x = true → nsP.contains x = true) ∧
    (∀ x, Trunc.names.contains x = true → nsP.contains x = true) ∧
    (∀ x, Rsh.names.contains x = true → nsP.contains x = true) ∧
    (∀ x, Lsh.names.contains x = true → nsP.contains x = true) :=
  ⟨sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide),
    sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide)⟩

theorem sqrWX_eq : NatSqr.sqrWX = 70592 := by simp only [NatSqr.sqrWX, sqrW, ksqrW]

theorem mulWX_eq : mulWX = 30208 := rfl

section
variable {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hwb in
theorem sn : StackNat.HypL impl R nsP 4208 24 := fun b L st n =>
  ens_widen hap subs.1 (StackNat.ensL impl hap R hgr hmc hwb b L st n)

include hmv hmk in
theorem tr : Trunc.Hyp2 impl R nsP 4208 64 := fun b L z zl zc x xl xc n =>
  ens_widen hap subs.2.2.2.1 (Trunc.ens impl hap R hmk hmv b L z zl zc x xl xc n)

include hmv hmk in
theorem rh : Rsh.Hyp impl R nsP 4240 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2.2.2.2.1 (Rsh.ens impl hap R hmk hmv b L z zl zc x xl xc sh)

include hmc hmv hmk in
theorem lh : Lsh.Hyp2 impl R nsP 4256 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2.2.2.2.2 (Lsh.ens impl hap R hmk hmv hmc b L z zl zc x xl xc sh)

end

end FvModexp.Arm64.CalleeInst
