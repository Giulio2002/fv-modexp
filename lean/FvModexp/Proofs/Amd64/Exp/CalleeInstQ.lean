import FvModexp.Proofs.Amd64.Exp.EnsWiden
import FvModexp.Proofs.Amd64.Exp.P2PreDefs
import FvModexp.Proofs.Amd64.Exp.P2W4Defs
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Nat.StackNatX
import FvModexp.Proofs.Amd64.NatQ.NatSqr
import FvModexp.Proofs.Amd64.NatQ.NatMul
import FvModexp.Proofs.Amd64.Nat.Trunc
import FvModexp.Proofs.Amd64.Nat.Lsh
import FvModexp.Proofs.Amd64.Nat.RshDefs

set_option autoImplicit false

/-!
# The exp layer (amd64): CLOSED Q-form callee summaries (agent divmc s75; amd64 twin of Arm64/Exp/CalleeInstQ +
CalleeInstP2Q)

`nsQ` = `(*stack).nat` + Q-form `nat.sqr` + Q-form `nat.mul` + `nat.trunc` + `nat.shr` + `nat.shl` (all amd64), a
sub-list of `LibW.names` that leaves out every power-of-two / window / exp function. Each callee's own `Ensures` is
moved to `nsQ` with `EnsWiden.ens_widen`:
* `sn : StackNatX.HypQ impl R nsQ 4192 24`  (`StackNatX.hypQ`)
* `sq : P2Pre.SqrE impl R nsQ W`  for EVERY window `W` (`Q.NatSqr.ens`; `ModInv.SqrE` is the same definition body)
* `mu : Q.DivRec.MulHypQE impl R nsQ W`  for every `W` (`Q.NatMul.hypQE`)
* `tr : Trunc.Hyp2 impl R nsQ 4192 64`  (`Trunc.ens`)
* `lh : Lsh.Hyp2 impl R nsQ 4248 64` (`Rsh.names` ⊆ nsQ via `subs`; the `Rsh.Hyp` instance is infra's)
* `sub` (nsQ ⊆ LibW.names), `nf2`/`nf4`/`nfP`/`nfD` (P2W2/P2W4/P2Pre/expNNPowerOfTwo ∉ nsQ),
  `widen` (any `ns ⊆ nsQ` ⊆ any caller list).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Amd64.EnsWiden (ens_widen)

namespace FvModexp.Amd64.CalleeInstQ

def nsQ : List String :=
  StackNat.names ++ Q.NatSqr.names ++ Q.NatMul.names ++ Trunc.names ++ Rsh.names ++ Lsh.names

/-- `∀ x ∈ ns, x ∈ ms` from a decidable `List.all` check. -/
theorem sub_of_all {ns ms : List String} (h : ns.all (fun x => ms.contains x) = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (List.contains_iff_mem.1 hx)

set_option maxHeartbeats 64000000 in
theorem sub : ∀ x, nsQ.contains x = true → LibW.names.contains x = true := sub_of_all (by decide)

set_option maxHeartbeats 64000000 in
theorem subs : (∀ x, StackNat.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Q.NatSqr.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Q.NatMul.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Trunc.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Rsh.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Lsh.names.contains x = true → nsQ.contains x = true) :=
  ⟨sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide),
    sub_of_all (by decide), sub_of_all (by decide)⟩

set_option maxHeartbeats 64000000 in
theorem nf2 : nsQ.contains P2W2.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nf4 : nsQ.contains P2W4.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nfP : nsQ.contains P2Pre.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nfD : nsQ.contains NHyp.fnP2 = false := by decide

section
variable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hwb in
theorem sn : StackNatX.HypQ impl R nsQ 4192 24 := fun H b L st n =>
  ens_widen hap subs.1 (StackNatX.ensQ impl hap R hgr hmc hwb H b L st n)

include hgr hmc hmv hmk hwb in
theorem sq (W : Nat) : P2Pre.SqrE impl R nsQ W := fun H b L zp zl zc st xp xl xc =>
  ens_widen hap subs.2.1 (Q.NatSqr.ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc)

include hgr hmc hmv hmk hwb in
theorem mu (W : Nat) : Q.DivRec.MulHypQE impl R nsQ W := fun H b L z zl zc st x xl xc yp yl yc =>
  ens_widen hap subs.2.2.1 (Q.NatMul.hypQE impl hap R hmk hgr hmc hmv hwb W H b L z zl zc st x xl xc yp yl yc)

include hmv hmk in
theorem tr : Trunc.Hyp2 impl R nsQ 4192 64 := fun b L z zl zc x xl xc n =>
  ens_widen hap subs.2.2.2.1 (Trunc.ens impl hap R hmk hmv b L z zl zc x xl xc n)

include hmc hmv hmk in
theorem lh : Lsh.Hyp2 impl R nsQ 4248 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2.2.2.2.2 (Lsh.ens impl hap R hmk hmv hmc b L z zl zc x xl xc sh)

end

end FvModexp.Amd64.CalleeInstQ
