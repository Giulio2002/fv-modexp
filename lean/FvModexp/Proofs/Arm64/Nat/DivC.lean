import FvModexp.Proofs.Arm64.Nat.DivR
import FvModexp.Proofs.Arm64.Nat.NatMulXE

/-!
# `nat.div` (arm64) CLOSED: no open callee premise (asm s31)

`ensC` = `NatDiv.ensR` with divmc's `NatMul.hypXE` (program `NatMul.names`, window `mulWX`, above `88`) for the
`nat.mul` premise of `divRecursiveStep`. Remaining hypotheses: only the live runtime contracts on
`Extracted.program.ofImpl impl` (growslice, memclrNoHeapPointers, gcWriteBarrier2, makeslice, memmove, MemmoveZeroLive).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatDiv

theorem mul_ns : NatMul.names.contains DivRec.fn = false := by decide

theorem mul_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn ((Extracted.program.onlySegments NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))

/-- **`nat.div`** (arm64), every callee discharged -/
theorem ensC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHyp impl R names 41504 112 (cost DivRec.drsC) :=
  ensR impl hap R NatMul.names mul_ns (mul_code impl hap)
    (NatMul.hypXE impl hap R hmk0 hgr hmc hmv0 hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmk0 hmv0 hmz0

/-- **`nat.div`** (arm64), every callee discharged, `StackBackL` form (`ExpHyp.DivHypL`) -/
theorem ensCL (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypL impl R names 41504 112 (cost DivRec.drsC) :=
  ensRL impl hap R NatMul.names mul_ns (mul_code impl hap)
    (NatMul.hypXE impl hap R hmk0 hgr hmc hmv0 hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmk0 hmv0 hmz0

end FvModexp.Arm64.NatDiv
