import FvModexp.Proofs.Arm64.Nat.MulStep
import FvModexp.Proofs.Arm64.Nat.KMulStep
import FvModexp.Proofs.Arm64.Nat.MulIMul

set_option autoImplicit false

/-!
# The multiplication SCC `{nat.mul, karatsuba, (*Int).mul}` (arm64): all three summaries by `Summary.induction_mutual`

`scc`: every member's summary on `LibMul.program`, from `mul_step` (`nat.mul`), `kar_step` (`karatsuba`) and
`imul_step` (`(*Int).mul`) with the measure `μ` (MulDefs); premises are the live runtime contracts only.
(Structure as this repo's `SqrSCC.scc`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

theorem scc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ∀ j : Mem, Summary (LibMul.program.link impl) (entryOf j) (preOf R j) (postOf R j) :=
  Summary.induction_mutual μ fun m ih j => by
    rcases j with ⟨k, a⟩
    cases k
    · exact mul_step impl hap R hmk hmv hgr hmc hwb m ih a
    · exact kar_step impl hap R hmk hgr hmc hmv hwb m ih a
    · exact imul_step impl hap R hwb m ih a

end FvModexp.Arm64.NatMul
