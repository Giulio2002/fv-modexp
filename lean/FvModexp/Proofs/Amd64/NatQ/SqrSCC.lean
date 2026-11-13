import FvModexp.Proofs.Amd64.NatQ.SqrStep
import FvModexp.Proofs.Amd64.NatQ.KSqrStep

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/SqrSCC.lean — TIGHT COSTS] The squaring SCC
`{nat.sqr, karatsubaSqr}` (amd64): both summaries by `Summary.induction_mutual`

`scc`: every member's summary on `LibSqr.program`, from `sqr_step` (`nat.sqr`, measure `2·len x + 1`) and `ksqr_step`
(`karatsubaSqr`, measure `2·len x`); premises are the live runtime contracts only.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem scc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ∀ j : Mem, Summary (LibSqr.program.link impl) (entryOf j) (preOf R H j) (postOf R H j) :=
  Summary.induction_mutual μ fun m ih j => by
    rcases j with ⟨k, a⟩
    cases k
    · exact sqr_step impl hap R hmk hgr hmc hwb m ih a
    · exact ksqr_step impl hap R hmk hgr hmc hmv hwb m ih a

end FvModexp.Amd64.Q.NatSqr
