import FvModexp.Proofs.Arm64.Exp.CalleeInst0
import FvModexp.Proofs.Arm64.Nat.SqrHypX
import FvModexp.Proofs.Arm64.Nat.MulHypX

set_option autoImplicit false

/-!
# The exp layer (arm64): CLOSED callee summaries for infra's rows (agent infra)

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

section
variable {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
  (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
  (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
  (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
  (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
  (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
include hap

include hgr hmc hmv hmk hwb in
theorem sq : SqrHypX impl R nsP NatSqr.sqrWX 64 sqrC := fun b L z zl zc st x xl xc =>
  ens_widen hap subs.2.1 (NatSqr.hypX impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc)

include hgr hmc hmv hmk hwb in
theorem mu : MulHypX impl R nsP mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
  ens_widen hap subs.2.2.1 (NatMul.hypX impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc y yl yc)


end

theorem sqm : ∀ ℓ a a', a ≤ a' → sqrC ℓ a ≤ sqrC ℓ a' := fun ℓ _ _ h => sqrC_mono (Nat.le_refl ℓ) h

theorem mum : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mulC ℓ a c ≤ mulC ℓ a' c' :=
  fun ℓ _ _ _ _ h1 h2 => mulC_mono (Nat.le_refl ℓ) h1 h2

end FvModexp.Arm64.CalleeInst
