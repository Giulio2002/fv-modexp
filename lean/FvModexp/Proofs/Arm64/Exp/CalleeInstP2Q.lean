import FvModexp.Proofs.Arm64.Exp.CalleeInstQ
import FvModexp.Proofs.Arm64.Exp.P2W2Defs
import FvModexp.Proofs.Arm64.Exp.P2W4Defs
import FvModexp.Proofs.Arm64.Exp.P2PreDefs
import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# The power-of-two chain's closed Q-form callees (arm64; divmc s42, TIGHT COSTS)

On infra's `CalleeInstQ.nsQ` (divmc's Q-form `nat.sqr`/`nat.mul`): the Q-form `(*stack).nat` (`StackNatX.hypQ`),
`rsh`, and the facts that `nsQ` leaves out the power-of-two functions (as `P2Wit.nf*` for `nsP`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)

namespace FvModexp.Arm64.P2WitQ

open FvModexp.Arm64.CalleeInstQ (nsQ)
open FvModexp.Arm64.CalleeInst (sub_of_all)

set_option maxHeartbeats 64000000 in
theorem nf2 : nsQ.contains P2W2.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nf4 : nsQ.contains P2W4.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nfP : nsQ.contains P2Pre.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nfD : nsQ.contains NHyp.fnP2 = false := by decide

set_option maxHeartbeats 64000000 in
theorem subs : (∀ x, StackNat.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Rsh.names.contains x = true → nsQ.contains x = true) :=
  ⟨sub_of_all (by decide), sub_of_all (by decide)⟩

section
variable {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hwb in
theorem sn : StackNatX.HypQ impl R nsQ 4208 24 := fun H b L st n =>
  ens_widen hap subs.1 (StackNatX.ensQ impl hap R hgr hmc hwb H b L st n)

include hmv hmk in
theorem rh : Rsh.Hyp impl R nsQ 4240 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2 (Rsh.ens impl hap R hmk hmv b L z zl zc x xl xc sh)

end

end FvModexp.Arm64.P2WitQ
