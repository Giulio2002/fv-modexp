import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Exp.SubMod2NGEns
import FvModexp.Proofs.Amd64.Exp.SubMod2N
import FvModexp.Proofs.Amd64.Exp.SubMod2NGJ
import FvModexp.Proofs.Amd64.Exp.EvTrD
import FvModexp.Proofs.Amd64.Exp.LibNE
import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Amd64.Exp.ModInvDefs
import FvModexp.Proofs.Amd64.Nat.TruncE0
import FvModexp.Proofs.Amd64.Nat.NatAdd0
import FvModexp.Proofs.Amd64.Nat.StackNat

set_option autoImplicit false

/-!
# amd64 callee instances for `nat.expNNEven` / `nat.modularInverseModPowerOfTwo` / `nat.subMod2N` (agent divmc s78)

Closed instances (coordinator "CALLEE-INSTANCE LAYER re-split") of the callee premises of asm's `ExpEven.full` and
infra's `ModInv.ens`, on divmc's `CalleeInstQ.nsQ` where a name list is taken:
* `se : SubMod2N.EnsG impl R` (infra's `SubMod2N.ensG` with `nat.trunc` = `CalleeInstQ.tr`),
* `sb : SubMod2N.SubHypR0 impl R` (`NatSub.ensR0`), `ad : SubMod2N.AddHypR impl R` (`NatAdd.ensR`),
* `t0 : ExpEven.TrHyp0 impl R nsQ 4192 64` (asm's `Trunc.ens0`, widened), `a0 : ExpEven.AddHypR0 impl R` (`NatAdd.ensR0`),
* `sl : StackNat.HypL impl R nsQ 4192 24` (`StackNat.ensL`, widened),
* name-list facts `subNE : nsQ ⊆ LibNE.names`, `nfE`/`nfM`/`nfS` (`nat.expNNEven` / `modInv` / `subMod2N` ∉ nsQ).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp
open FvModexp.Amd64.EnsWiden (ens_widen)

namespace FvModexp.Amd64.CalleeInstQ

set_option maxHeartbeats 64000000 in
theorem subNE : ∀ x, nsQ.contains x = true → LibNE.names.contains x = true := sub_of_all (by decide)

set_option maxHeartbeats 64000000 in
theorem nfE : nsQ.contains ExpEven.fn = false := by decide

set_option maxHeartbeats 64000000 in
theorem nfM : nsQ.contains ModInv.fn = false := by decide

set_option maxHeartbeats 64000000 in
theorem nfS : nsQ.contains SubMod2N.fn = false := by decide

variable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hmv hmk hgr in
/-- `nat.subMod2N`, general form (any capacity of `z`) -/
theorem se : SubMod2N.EnsG impl R :=
  SubMod2N.ensG impl hap R sub nfS (by decide) (by decide) (tr hap hmv hmk) hmk hmv hgr

include hmv hmk in
theorem sb : SubMod2N.SubHypR0 impl R := SubMod2N.subHypR0_of impl hap R hmk hmv

include hmv hmk in
theorem ad : SubMod2N.AddHypR impl R := SubMod2N.addHypR_of impl hap R hmk hmv

include hmv hmk in
/-- `nat.trunc` with an empty-tolerant `x` on `nsQ` -/
theorem t0 : ExpEven.TrHyp0 impl R nsQ 4192 64 := fun b L z zl zc x xl xc n =>
  ens_widen hap subs.2.2.2.1 (Trunc.ens0 impl hap R hmk hmv b L z zl zc x xl xc n)

include hmv hmk in
/-- `nat.add` with empty-tolerant operands -/
theorem a0 : ExpEven.AddHypR0 impl R := fun b L zp zl zc xp xl xc yp yl yc =>
  NatAdd.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

include hgr hmc hwb in
/-- `(*stack).nat` in the `StackBackL` form on `nsQ` -/
theorem sl : StackNat.HypL impl R nsQ 4192 24 := fun b L st n =>
  ens_widen hap subs.1 (StackNat.ensL impl hap R hgr hmc hwb b L st n)

end FvModexp.Amd64.CalleeInstQ
