import FvModexp.Proofs.Amd64.NatQ.MulStep
import FvModexp.Proofs.Amd64.NatQ.KMulStep
import FvModexp.Proofs.Amd64.NatQ.MulIMul

set_option autoImplicit false

/-!
# [amd64 port (divmc s54) of the Q-form Arm64/NatQ/MulSCC.lean — TIGHT COSTS] The multiplication SCC `{nat.mul, karatsuba, (*Int).mul}` (amd64): all three summaries by `Summary.induction_mutual`

`scc`: every member's summary on `LibMul.program`, from `mul_step` (`nat.mul`), `kar_step` (`karatsuba`) and
`imul_step` (`(*Int).mul`) with the measure `μ` (MulDefs); premises are the live runtime contracts only.
(Structure as this repo's amd64 `SqrSCC.scc`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem scc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ∀ j : Mem, Summary (LibMul.program.link impl) (entryOf j) (preOf R H j) (postOf R H j) :=
  Summary.induction_mutual μ fun m ih j => by
    rcases j with ⟨k, a⟩
    cases k
    · exact mul_step impl hap R hmk hmv hgr hmc hwb m ih a
    · exact kar_step impl hap R hmk hgr hmc hmv hwb m ih a
    · exact imul_step impl hap R hwb m ih a

end FvModexp.Amd64.Q.NatMul
