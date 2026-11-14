import FvModexp.Proofs.Arm64.Exp.CalleeInst0
import FvModexp.Proofs.Arm64.NatQ.SqrHypQ
import FvModexp.Proofs.Arm64.NatQ.MulHypQ

set_option autoImplicit false

/-!
# The exp layer (arm64): CLOSED Q-form callee summaries for infra's rows (agent infra, s45 TIGHT COSTS)

`nsQ` = `CalleeInst.nsP` with divmc's Q-form `nat.sqr` / `nat.mul` (`Q.NatSqr.hypQ` cost `sqrCQ`, window `sqrWX`;
`Q.NatMul.hypQ` cost `mulCQ`, window `mulWX`), each moved to `nsQ` with `EnsWiden.ens_widen`.
Used by `ModInvRow` (and the P2 rows once their loops are in Q-form).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)

namespace FvModexp.Arm64.CalleeInstQ

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.CalleeInst (sub_of_all)

def nsQ : List String :=
  StackNat.names ++ Q.NatSqr.names ++ Q.NatMul.names ++ Trunc.names ++ Rsh.names ++ Lsh.names

set_option maxHeartbeats 64000000 in
theorem sub : ∀ x, nsQ.contains x = true → LibW.names.contains x = true := sub_of_all (by decide)

set_option maxHeartbeats 64000000 in
theorem subs : (∀ x, Q.NatSqr.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Q.NatMul.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Trunc.names.contains x = true → nsQ.contains x = true) ∧
    (∀ x, Lsh.names.contains x = true → nsQ.contains x = true) :=
  ⟨sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide), sub_of_all (by decide)⟩

section
variable {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hmv hmk hwb in
theorem sq : SqrHypQ impl R nsQ NatSqr.sqrWX 64 sqrCQ := fun H b L z zl zc st x xl xc =>
  ens_widen hap subs.1 (Q.NatSqr.hypQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc)

include hgr hmc hmv hmk hwb in
theorem mu : MulHypQ impl R nsQ mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
  ens_widen hap subs.2.1 (Q.NatMul.hypQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc y yl yc)

include hmv hmk in
theorem tr : Trunc.Hyp2 impl R nsQ 4208 64 := fun b L z zl zc x xl xc n =>
  ens_widen hap subs.2.2.1 (Trunc.ens impl hap R hmk hmv b L z zl zc x xl xc n)

include hmc hmv hmk in
theorem lh : Lsh.Hyp2 impl R nsQ 4256 64 := fun b L z zl zc x xl xc sh =>
  ens_widen hap subs.2.2.2 (Lsh.ens impl hap R hmk hmv hmc b L z zl zc x xl xc sh)

end

theorem sqm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrCQ a' := fun _ _ h => sqrCQ_mono h

theorem mum : ∀ a a' c c', a ≤ a' → c ≤ c' → mulCQ a c ≤ mulCQ a' c' := fun _ _ _ _ h1 h2 => mulCQ_mono h1 h2

end FvModexp.Arm64.CalleeInstQ
