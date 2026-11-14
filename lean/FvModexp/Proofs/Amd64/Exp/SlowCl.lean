import FvModexp.Proofs.Amd64.Exp.SlowSumQ
import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.NatQ.DivCG

set_option autoImplicit false

/-!
# **`nat.expNNSlow`** amd64 — the CLOSED callee shapes (agent expmc s82)

* `Q.ExpSlow.hypCl : NHyp.SlowHypQ impl R LibW.names 41952 112 need needH (costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ))`
  — only the live runtime contracts as premises: `nat.sqr` = `sqG` of divmc's `CalleeInstQ.sq 7104`, `nat.mul` =
  `CalleeInstQ.mu mulWX64`, `nat.div` = asm's `Q.NatDiv.ensCLG` (window 41512), all widened to `nsS = nsQ ++ NatDiv.names`
  (`⊆ LibW.names`, without `nat.expNNSlow`). Frame depth `41952 = 41512 + 0x1b8`.
* `Q.ExpSlow.slowCl : NHyp.SlowHyp …` = `slow_of_Q hypCl` (for `ExpN.DHyps.slow`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.ExpSlow

open FvModexp.Amd64.ExpSlow

/-- the callee program of `nat.expNNSlow`'s three calls -/
def nsS : List String := CalleeInstQ.nsQ ++ Q.NatDiv.names

set_option maxHeartbeats 64000000 in
theorem nsS_sub : ∀ x, nsS.contains x = true → LibW.names.contains x = true :=
  CalleeInstQ.sub_of_all (by decide +kernel)

set_option maxHeartbeats 64000000 in
theorem nsS_nf : nsS.contains fn = false := by decide +kernel

set_option maxHeartbeats 64000000 in
theorem nsQ_sub : ∀ x, CalleeInstQ.nsQ.contains x = true → nsS.contains x = true :=
  CalleeInstQ.sub_of_all (by decide +kernel)

set_option maxHeartbeats 64000000 in
theorem div_sub : ∀ x, Q.NatDiv.names.contains x = true → nsS.contains x = true :=
  CalleeInstQ.sub_of_all (by decide +kernel)

set_option maxHeartbeats 64000000 in
theorem sqr_sub : ∀ x, Q.NatSqr.names.contains x = true → nsS.contains x = true :=
  CalleeInstQ.sub_of_all (by decide +kernel)

section
variable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap hgr hmc hmv hmz hmk hwb

/-- **`nat.expNNSlow`** (amd64), closed: only the live runtime contracts -/
theorem hypCl :
    NHyp.SlowHypQ impl R LibW.names 41952 112 need needH (costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) :=
  hyp hap nsS_sub nsS_nf
    (sqG hap sqr_sub fun H b L zp zl zc st xp xl xc =>
      EnsWiden.ens_widen hap nsQ_sub (CalleeInstQ.sq hap hgr hmc hmv hmk hwb 7104 H b L zp zl zc st xp xl xc))
    (Nat.le_refl _)
    (fun H b L z zl zc st x xl xc yp yl yc =>
      EnsWiden.ens_widen hap nsQ_sub (CalleeInstQ.mu hap hgr hmc hmv hmk hwb mulWX64 H b L z zl zc st x xl xc yp yl yc))
    (Nat.le_refl _)
    (fun H b L z zl zc st z2 z2l z2c u ul uc v vl vc =>
      EnsWiden.ens_widen hap div_sub
        (Q.NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz H b L z zl zc st z2 z2l z2c u ul uc v vl vc))
    hmk hmv hmz (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **`nat.expNNSlow`** (amd64), closed, in the level-cost form `NHyp.SlowHyp` (for `ExpN.DHyps.slow`) -/
theorem slowCl :
    NHyp.SlowHyp impl R LibW.names 41952 112 need (slowBr (costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) needH) :=
  slow_of_Q (hypCl hap hgr hmc hmv hmz hmk hwb)

end

end FvModexp.Amd64.Q.ExpSlow
