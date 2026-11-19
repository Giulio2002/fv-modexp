import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.MulHypX
import FvModexp.Proofs.Arm64.Nat.DrsDefs

set_option autoImplicit false

/-!
# `nat.mul` (arm64) in asm's premise form `DivRec.MulHypXE` (divRecursiveStep's `qhatv.mul(stk, qhat, v[:s])`)

`NatMul.hypXE` = `NatMul.hypXE0` with the pre weakened by `MulPre.to0` (`RdIn` → `RdIn0`); `EvenHyp.ExactE` and asm's
`DivRec.ExactR` have the same body. A separate module so that the `nat.mul` chain does not import asm's.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.EvenHyp

/-- **`nat.mul`** (arm64) as `DivRec.MulHypXE` at the window `mulWX`, `above = 88`, cost `mulC` -/
theorem hypXE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    DivRec.MulHypXE impl R names mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
  (hypXE0 impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc y yl yc).mono_ret
    (fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.to0, h2, h3, h4⟩) (fun _ _ _ _ hq => hq)

end FvModexp.Arm64.NatMul
